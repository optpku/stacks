module

public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Groupoid.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian automorphism groups in fibers

The condition in this module belongs to a projection fibred in groupoids, not
to a particular site or a bundled stack.  It supplies the canonical
multiplicative commutative group of automorphisms in every fiber.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

namespace Functor.IsFibered.InGroupoids

variable {C : Type uC} {S : Type uS}
variable [Category.{vC} C] [Category.{vS} S]

/-- The abelianity hypothesis in Lemma 8.11.8 (tag 0CJY): a category fibred in groupoids has
abelian automorphism groups when the endomorphisms of every object in every standard fiber
commute. -/
@[stacks 0CJY "abelian automorphism groups in fibres"]
class Automorphism.IsAbelian
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] : Prop where
  /-- Endomorphisms of one fiber object commute under categorical composition. -/
  comm {U : C} (x : p.Fiber U) (f g : x ⟶ x) : f ≫ g = g ≫ f

variable (p : S ⥤ C) [Functor.IsFibered.InGroupoids p]
variable [Automorphism.IsAbelian p]

/-- The canonical multiplicative commutative-group structure on the
automorphisms of an object of a fiber. -/
@[stacks 0CJY "commutative automorphism group instance"]
noncomputable instance Automorphism.endCommGroup {U : C} (x : p.Fiber U) :
    CommGroup (End x) :=
  End.commGroupOfCompComm x
    (fun f g ↦ Automorphism.IsAbelian.comm x f g)

/-- The automorphism group of a fiber object, packaged as an object of
`CommGrpCat`. -/
@[stacks 0CJY "commutative automorphism group object"]
noncomputable def Automorphism.commGrp {U : C} (x : p.Fiber U) : CommGrpCat :=
  CommGrpCat.of (End x)

end Functor.IsFibered.InGroupoids

end CategoryTheory
