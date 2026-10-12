/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Operations
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal

/-!
# Changing the ideal in a quotient complex

An inclusion `I ≤ J` induces the canonical map `K / IK ⟶ K / JK`.  The two quotient complexes
have different quotient-ring scalar structures, so the canonical comparison is owned at their
common scalar-restricted `A`-linear view.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace HomologicalComplex.ModIdeal

variable {A : Type u} [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- The degreewise `A`-linear quotient map induced by an inclusion of ideals. -/
def restrictedOfLELinear {I J : Ideal A} (h : I ≤ J)
    (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    (restrictedComplex I K).X i →ₗ[A] (restrictedComplex J K).X i :=
  Submodule.factor (R := A) (M := K.X i) (Submodule.smul_mono_left h)

/-- On representatives, changing from the quotient by `I` to the quotient by `J` preserves the
ambient element. -/
@[simp]
theorem restrictedOfLELinear_mk {I J : Ideal A} (h : I ≤ J)
    (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) (x : K.X i) :
    restrictedOfLELinear h K i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := sorry

/-- The degreewise quotient maps induced by `I ≤ J` commute with the quotient differentials. -/
theorem restrictedOfLE_comm {I J : Ideal A} (h : I ≤ J)
    (K : HomologicalComplex (ModuleCat.{v} A) c) (i j : ι) (hij : c.Rel i j) :
    ModuleCat.ofHom
        (X := (restrictedComplex I K).X i) (Y := (restrictedComplex J K).X i)
        (restrictedOfLELinear h K i) ≫ (restrictedComplex J K).d i j =
      (restrictedComplex I K).d i j ≫
        ModuleCat.ofHom
          (X := (restrictedComplex I K).X j) (Y := (restrictedComplex J K).X j)
          (restrictedOfLELinear h K j) := sorry

/-- The canonical scalar-restricted map `K / IK ⟶ K / JK` induced by `I ≤ J`. -/
@[stacks 00DV "change of ideal on a quotient complex"]
def restrictedOfLE {I J : Ideal A} (h : I ≤ J)
    (K : HomologicalComplex (ModuleCat.{v} A) c) :
    restrictedComplex I K ⟶ restrictedComplex J K where
  f i := ModuleCat.ofHom
    (X := (restrictedComplex I K).X i) (Y := (restrictedComplex J K).X i)
    (restrictedOfLELinear h K i)
  comm' i j hij := restrictedOfLE_comm h K i j hij

/-- On quotient representatives, the canonical change-of-ideal map preserves the ambient
element. -/
@[simp]
theorem restrictedOfLE_mk {I J : Ideal A} (h : I ≤ J)
    (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) (x : K.X i) :
    (restrictedOfLE h K).f i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := sorry

/-- Changing along the identity inclusion gives the identity morphism. -/
@[simp]
theorem restrictedOfLE_id (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{v} A) c) :
    restrictedOfLE (le_refl I) K = 𝟙 (restrictedComplex I K) := sorry

/-- Change-of-ideal maps compose according to transitivity of ideal inclusion. -/
@[simp]
theorem restrictedOfLE_comp {I J L : Ideal A} (hIJ : I ≤ J) (hJL : J ≤ L)
    (K : HomologicalComplex (ModuleCat.{v} A) c) :
    restrictedOfLE hIJ K ≫ restrictedOfLE hJL K =
      restrictedOfLE (hIJ.trans hJL) K := sorry

/-- Change of ideal is natural with respect to morphisms of homological complexes. -/
theorem restrictedOfLE_naturality {I J : Ideal A} (h : I ≤ J)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (φ : K ⟶ L) :
    restrictedMap I φ ≫ restrictedOfLE h L =
      restrictedOfLE h K ≫ restrictedMap J φ := sorry

/-- The canonical change-of-ideal maps form a natural transformation between scalar-restricted
quotient functors. -/
@[stacks 00DV "change-of-ideal natural transformation"]
def restrictedNatTrans {I J : Ideal A} (h : I ≤ J) :
    restrictedFunctor.{u, v, w} (c := c) I ⟶ restrictedFunctor J where
  app K := restrictedOfLE h K
  naturality _ _ φ := restrictedOfLE_naturality h φ

end HomologicalComplex.ModIdeal
