module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ExactAdmissible
public import stacks_project.Chap56.Lemma_56_5_2_Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))

/- The exact-admissible functor API is owned by the quasicoherent-module library. -/
#check (AlgebraicGeometry.Scheme.QCoh.ExactAdmissible x y :
  (Scheme.QCoh X ⥤ Scheme.QCoh Y) → Prop)
#check (AlgebraicGeometry.Scheme.QCoh.exactAdmissible_iff x y :
  ∀ F : Scheme.QCoh X ⥤ Scheme.QCoh Y,
    ExactAdmissible x y F ↔
      Admissible x y F ∧ exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F)
#check (AlgebraicGeometry.Scheme.QCoh.ExactCoproductLinearFunctor x y : Type (u + 1))
#check (AlgebraicGeometry.Scheme.QCoh.exactCoproductLinearFunctor_property x y :
  ∀ F : ExactCoproductLinearFunctor x y, ExactAdmissible x y F.obj)

end AlgebraicGeometry.Scheme.QCoh
