package inge2.dataflow.pointstoanalysis;

import soot.jimple.*;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JimpleLocal;

import java.util.HashSet;
import java.util.Set;

public class PointsToVisitor extends AbstractStmtSwitch<Void> {

    private final PointsToGraph pointsToGraph;

    public PointsToVisitor(PointsToGraph pointsToGraph) {
        this.pointsToGraph = pointsToGraph;
    }

    @Override
    public void caseAssignStmt(AssignStmt stmt) {
        boolean isLeftLocal = stmt.getLeftOp() instanceof JimpleLocal;
        boolean isRightLocal = stmt.getRightOp() instanceof JimpleLocal;

        boolean isLeftField = stmt.getLeftOp() instanceof JInstanceFieldRef;
        boolean isRightField = stmt.getRightOp() instanceof JInstanceFieldRef;

        boolean isRightNew = stmt.getRightOp() instanceof AnyNewExpr;

        if (isRightNew) { // x = new A()
            processNewObject(stmt);
        } else if (isLeftLocal && isRightLocal) { // x = y
            processCopy(stmt);
        } else if (isLeftField && isRightLocal) { // x.f = y
            processStore(stmt);
        } else if (isLeftLocal && isRightField) { // x = y.f
            processLoad(stmt);
        }
    }

    private void processNewObject(AssignStmt stmt) {
        String leftVariableName = stmt.getLeftOp().toString();
        Node nodeName = pointsToGraph.getNodeName(stmt);
        Set<Node> graphNodes = new HashSet<>();
        graphNodes.add(nodeName);
        pointsToGraph.setNodesForVariable(leftVariableName, graphNodes);
    }

    private void processCopy(AssignStmt stmt) {
        String leftVariableName = stmt.getLeftOp().toString();
        String rightVariableName = stmt.getRightOp().toString();

        Set<Node> graphNodes = pointsToGraph.getNodesForVariable(rightVariableName);
        pointsToGraph.setNodesForVariable(leftVariableName, graphNodes);

    }

    private void processStore(AssignStmt stmt) { // x.f = y
        JInstanceFieldRef leftFieldRef = (JInstanceFieldRef) stmt.getLeftOp();
        String leftVariableName = leftFieldRef.getBase().toString();
        String fieldName = leftFieldRef.getField().getName();
        String rightVariableName = stmt.getRightOp().toString();

        Set<Node> reachableByRightNode = pointsToGraph.getNodesForVariable(rightVariableName);
        Set<Node> reachableByLeftNode = pointsToGraph.getNodesForVariable(leftVariableName);

        for (Node leftNode : reachableByLeftNode) {
            for (Node rightNode : reachableByRightNode) {
                pointsToGraph.addEdge(leftNode, fieldName, rightNode);
            }
        }
    }

    private void processLoad(AssignStmt stmt) { // x = y.f
        String leftVariableName = stmt.getLeftOp().toString();
        JInstanceFieldRef rightFieldRef = (JInstanceFieldRef) stmt.getRightOp();
        String rightVariableName = rightFieldRef.getBase().toString();
        String fieldName = rightFieldRef.getField().getName();

        Set<Node> reachableByRightNode = pointsToGraph.getNodesForVariable(rightVariableName);
        Set<Node> graphNodes = new HashSet<>();
        for (Node node : reachableByRightNode) {
            graphNodes.addAll(pointsToGraph.getReachableNodesByField(node, fieldName));
        }

        pointsToGraph.setNodesForVariable(leftVariableName, graphNodes);
    }
}
