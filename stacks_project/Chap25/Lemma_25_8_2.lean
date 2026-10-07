module

public import ReasLib.CategoryTheory.Sites.Hypercovering.InternalHom
import StacksCheckRecall

/-!
# Restriction along a finite inclusion

Finiteness means finitely many nondegenerate simplices, and nonemptiness means the existence of a
vertex; mathlib derives the corresponding objectwise facts automatically.
-/

open CategoryTheory

/- Lemma 25.8.2 (01GN): restriction in degree zero along an inclusion of finite nonempty
simplicial sets is a covering morphism for every hypercovering. -/
@[stacks 01GN] #check @Hypercovering.InternalHom.PrecompZero.isCovering
