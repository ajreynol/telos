import TelosProofs.Rewriter

/-!
# Axiom audit

Fails the build if a main theorem depends on anything beyond Lean's standard
axioms (in particular `sorryAx`, or any newly declared one). If a theorem comes to use fewer
axioms, update the expected message.
-/

/--
info: 'Telos.rewrite_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Telos.rewrite_correct
