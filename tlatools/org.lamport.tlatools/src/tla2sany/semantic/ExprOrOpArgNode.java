// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;
import tlc2.synth.Visitor;

/**
 * This class represents a semantic node that is either an OpArgNode
 * or is the root node of an expression (ExprNode).
 *
 * The reason both kinds of nodes are classified together in this
 * abstract class is that they can both be used as arguments to
 * operators and in substitutions.
 *
 * Extended by ExprNode and OpArgNode
 *
 * Further extended by AtNode, DecimalNode, LetInNode, NumeralNode,
 *                     OpApplNode, StringNode, SubstInNode
 */
public abstract class ExprOrOpArgNode extends LevelNode {

  ExprOrOpArgNode(int kind, TreeNode stn) { super(kind, stn); }

  /**
   * Makes a copy such that AST transformations do not affect the original.
   * Implementations may copy deeply or shallowly.
   * Requires access to private fields, so not a visitor.
   */
  public abstract ExprOrOpArgNode astCopy();

  public abstract <A> A accept(Visitor<A> visitor);
}
