/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_3_4_System
public import stacks_project.Chap85.Lemma_85_3_4_Comparison
public import stacks_project.Chap85.Lemma_85_3_4_Fiberwise

/-!
# Lemma 85.3.4

In Situation 85.3.3 there is an equivalence of categories between `Sh(C_total)` and the
category of systems `(F_n, F(φ))`. In particular, the topos `Sh(C_total)` depends only on
the topoi `Sh(C_n)` and the morphisms of topoi `f_φ`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Lemma 85.3.4 (1): in Situation 85.3.3 case A, sheaves on the total site `C_total` are
equivalent to systems `(F_n, F(φ))` with `F_n` a sheaf on `C.obj n` and
`F(φ) : F_m ⟶ f_{φ,*} F_n`, equivalently `f_φ⁻¹ F_m ⟶ F_n`, unital and functorial in simplex
operators. In particular `Sh(C_total)` depends only on the topoi `Sh(C.obj n)` and the
morphisms of topoi `f_φ`. -/
@[stacks 09WF]
def sheafEquivalence :
    Sheaf (topology C J) (Type w) ≌
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ toposMap C J φ) :=
  Equivalence.mk (toSheafSystem C J) (ofSheafSystem C J) (unitIso C J) (counitIso C J)

/-- The forward functor of `sheafEquivalence C J` extracts the system of degreewise restrictions
and `f_φ`-maps. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence C J).functor = toSheafSystem C J :=
  sorry

/-- The inverse functor of `sheafEquivalence C J` assembles a sheaf on `C_total` from a
system `(F_n, F(φ))`. -/
theorem sheafEquivalence_inverse :
    (sheafEquivalence C J).inverse = ofSheafSystem C J :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [IsFiberwiseSite F J]

/-- Lemma 85.3.4 (2): in Situation 85.3.3 case B, sheaves on the total site `Grothendieck F`
are equivalent to systems `(F_n, F(φ))` with `F_n` a sheaf on `F.obj (op n)` and
`F(φ) : F_m ⟶ f_{φ,*} F_n`, equivalently `f_φ⁻¹ F_m ⟶ F_n`, unital and functorial in simplex
operators. In particular `Sh(C_total)` depends only on the topoi `Sh(C_n)` and the morphisms
of topoi `f_φ`. -/
@[stacks 09WF]
def sheafEquivalence :
    Sheaf (topology F J) (Type w) ≌
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ toposMap F J φ) :=
  Equivalence.mk (toSheafSystem F J) (ofSheafSystem F J) (unitIso F J) (counitIso F J)

/-- The forward functor of `sheafEquivalence F J` extracts the system of degreewise restrictions
and `f_φ`-maps. -/
theorem sheafEquivalence_functor :
    (sheafEquivalence F J).functor = toSheafSystem F J :=
  sorry

/-- The inverse functor of `sheafEquivalence F J` assembles a sheaf on the total site from a
system `(F_n, F(φ))`. -/
theorem sheafEquivalence_inverse :
    (sheafEquivalence F J).inverse = ofSheafSystem F J :=
  sorry

end CategoryTheory.Grothendieck
