
import soot.*;
import soot.options.Options;
import soot.toolkits.graph.*;
import soot.toolkits.graph.pdg.*;
import soot.toolkits.scalar.SimpleLocalDefs;
import soot.toolkits.scalar.SimpleLocalUses;
import soot.toolkits.scalar.UnitValueBoxPair;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class Slicer {
    private static final String LINE_NUMBER_TAG = "LineNumberTag";

    private static void writeToFile(Set<String> lines, String filePath) throws IOException {
        BufferedWriter writer = new BufferedWriter(new FileWriter(filePath));

        if (lines != null) {
            for (String line : lines) {
                writer.write(line);
                writer.write("\t");
            }
        }

        writer.close();
    }

    private static Set<String> controlDependent = new HashSet<>();

    public static void main(String[] args) throws IOException {
        String classDirectory = args[0];
        String className = args[1];
        String outputFile = args[2];
        String lineNumber = args[3];
        String variableName = args[4];

        String methodName = "main";

        String sootClassPath = Scene.v().getSootClassPath() + File.pathSeparator + classDirectory;
        Scene.v().setSootClassPath(sootClassPath);

        Options.v().set_keep_line_number(true);
        Options.v().setPhaseOption("jb", "use-original-names");

        SootClass sootClass = Scene.v().loadClassAndSupport(className);
        Scene.v().loadNecessaryClasses();
        sootClass.setApplicationClass();

        SootMethod sootMethod = sootClass.getMethodByName(methodName);
        if (sootMethod == null) {
            throw new IllegalArgumentException("No method named " + methodName + " within a class " + className);
        }
        Body body = sootMethod.retrieveActiveBody();

        Set<Unit> statementsForLine = findStmt(body, Integer.parseInt(lineNumber));

        HashMutableDirectedGraph<Unit> pdg = calculatePDG(body);

        statementsForLine = reduceSet(pdg, body, statementsForLine, variableName);

        if (statementsForLine == null || statementsForLine.isEmpty()) {
            writeToFile(null, outputFile);
            return;
        }

        Set<Unit> sliceUnits = slice(pdg, statementsForLine);

        Set<String> lines = new HashSet<>();

        lines.add(lineNumber);

        for (Unit unit : sliceUnits) {
            if (!unit.hasTag(LINE_NUMBER_TAG)) {
                lines.add("entry");
                continue;
            }
            lines.add(String.valueOf(unit.getJavaSourceStartLineNumber()));
        }

        writeToFile(lines, outputFile);

//        printPDG(pdg);
    }

    private static void printPDG(HashMutableDirectedGraph<Unit> pdg) {

        Set<String> stringSet = new HashSet<>();

        System.out.println();
        for (Unit unit : pdg) {
            if (!unit.hasTag(LINE_NUMBER_TAG)) {
                continue;
            }
            int a = unit.getJavaSourceStartLineNumber();
            for (Unit successor : pdg.getSuccsOf(unit)) {
                if (!successor.hasTag(LINE_NUMBER_TAG)) {
                    continue;
                }

                int b = successor.getJavaSourceStartLineNumber();
                if (a == b) {
                    continue;
                }

                String edge = "\"" + a + "\"" + " -> " + "\"" + b + "\"";
                if (controlDependent.contains(getEdgeTag(unit, successor))) {
                    edge += " [ label=\"C\" ];";
                }

                stringSet.add(edge);
            }
        }

        for (String string : stringSet) {
            System.out.println(string);
        }
    }

    private static Set<Unit> slice(HashMutableDirectedGraph<Unit> pdg, Set<Unit> units) {
        Stack<Unit> workSet = new Stack<>();
        Set<Unit> slice = new HashSet<>();



        for (Unit unit : units) {
            workSet.push(unit);

            while (!workSet.empty()) {
                Unit currentNodeForIteration = workSet.pop();
                slice.add(currentNodeForIteration);
                for (Unit predecessor : pdg.getPredsOf(currentNodeForIteration)) {
                    if (slice.contains(predecessor)) {
                        continue;
                    }
                    workSet.push(predecessor);
                }
            }
        }

        return slice;
    }

    private static Set<Unit> reduceSet(
            HashMutableDirectedGraph<Unit> pdg,
            Body body,
            Set<Unit> statementsForLine,
            String variableName) {

        Set<Unit> auxiliarySet = new HashSet<>();
        for (Unit unit : statementsForLine) {
            for (ValueBox valueBox : unit.getUseBoxes()) {
                String stringValue = valueBox.getValue().toString();

                if (stringValue.equals(variableName)) {
                    auxiliarySet.add(unit);
                }
                if (stringValue.contains(variableName)) {
                    if (stringValue.contains("$")) {
                        stringValue = stringValue.replace("$", "");
                    }
                    if (stringValue.contains("#")) {
                        stringValue = stringValue.substring(0, stringValue.indexOf("#"));
                    }
                    if (stringValue.equals(variableName)) {
                        auxiliarySet.add(unit);
                    }
                }
            }
        }

        statementsForLine = auxiliarySet;
        auxiliarySet = new HashSet<>();
        EnhancedUnitGraph graph = new EnhancedUnitGraph(body);
        SimpleLocalDefs simpleLocalDefs = new SimpleLocalDefs(graph);



        for (Unit unit : statementsForLine) {
            for (Unit predecessor : pdg.getPredsOf(unit)) {
                if (controlDependent.contains(getEdgeTag(unit, predecessor))) {
                    auxiliarySet.add(predecessor);
                    continue;
                }

                Set<Local> locals = getLocalForVariable(body, variableName);
                if (locals.isEmpty()) {
                    System.err.println("Wrong variable name.");
                    return null;
                }

                for (Local local : locals) {
                    for (Unit dataDepPredecessor : simpleLocalDefs.getDefsOfAt(local, unit)) {
                        if (dataDepPredecessor == predecessor) {
                            auxiliarySet.add(dataDepPredecessor);
                        }
                    }
                }
            }
        }

        return auxiliarySet;
    }

    private static Set<Local> getLocalForVariable(Body body, String variableName) {
        Set<Local> locals = new HashSet<>();
        for (Local local : body.getLocals()) {
            if (local.getName().equals(variableName)) {
                locals.add(local);
                continue;
            }

            if (local.getName().contains(variableName) && local.getName().contains("#")) {
                String stringValue = local.getName();
                if (stringValue.contains("$")) {
                    stringValue = stringValue.replace("$", "");
                }
                if (stringValue.contains("#")) {
                    stringValue = stringValue.substring(0, stringValue.indexOf("#"));
                }
                if (stringValue.equals(variableName)) {
                    locals.add(local);
                }
            }
        }
        return locals;
    }

    private static Set<Unit> findStmt(Body body, int lineNumber) {
        Set<Unit> resultSet = new HashSet<>();
        for (Unit unit : body.getUnits()) {
            if (!unit.hasTag(LINE_NUMBER_TAG)) {
                continue;
            }

            if (lineNumber != unit.getJavaSourceStartLineNumber()) {
                continue;
            }

            resultSet.add(unit);
        }

        return resultSet;
    }

    private static HashMutableDirectedGraph<Unit> calculatePDG(Body body) {
        EnhancedUnitGraph graph = new EnhancedUnitGraph(body);
        MHGDominatorTree<Unit> postDomTree = new MHGDominatorTree<>(new MHGPostDominatorsFinder<>(graph));
        SimpleLocalDefs simpleLocalDefs = new SimpleLocalDefs(graph);
        SimpleLocalUses simpleLocalUses = new SimpleLocalUses(body, simpleLocalDefs);

        DominanceFrontier<Unit> dominanceFrontier = new CytronDominanceFrontier<>(postDomTree);

        HashMutableDirectedGraph<Unit> directedGraph = new HashMutableDirectedGraph<>();
        for (Unit unit : body.getUnits()) {
            addNode(directedGraph, unit);
            for (DominatorNode<Unit> dode : dominanceFrontier.getDominanceFrontierOf(postDomTree.getDode(unit))) {
                Unit frontierNode = dode.getGode();
                addNode(directedGraph, frontierNode);
                if (directedGraph.containsEdge(frontierNode, unit)) {
                    continue;
                }
                directedGraph.addEdge(frontierNode, unit);
                controlDependent.add(getEdgeTag(frontierNode, unit));
            }
            for (UnitValueBoxPair unitValueBoxPair : simpleLocalUses.getUsesOf(unit)) {
                addNode(directedGraph, unitValueBoxPair.unit);
                if (directedGraph.containsEdge(unit, unitValueBoxPair.unit)) {
                    continue;
                }
                directedGraph.addEdge(unit, unitValueBoxPair.unit);
            }
        }

        return directedGraph;
    }

    private static String getEdgeTag(Unit unitA, Unit unitB) {
        return unitA.toString() + " -> " + unitB.toString();
    }

    private static void addNode(HashMutableDirectedGraph<Unit> directedGraph, Unit unit) {
        if (directedGraph.containsNode(unit)) {
            return;
        }
        directedGraph.addNode(unit);
    }
}
