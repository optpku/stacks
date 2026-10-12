/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Remark_64_30_1_Comparison
public import stacks_project.Chap64.Remark_64_30_1_Coinvariants
public import stacks_project.Chap64.Remark_64_30_1_Extension
public import stacks_project.Chap64.Remark_64_30_1_Formula

/-!
# Observations on the abstract trace formula
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory.Functor
open ProfiniteGrp
open scoped AlgebraicGeometry Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (Spec (CommRingCat.of k))]
variable (etaBar : GeometricPoint X.left)

/-- Small étale Grothendieck topology of the underlying scheme of `X`. -/
abbrev smallEtale (X : SchemeOverField k) := X.left.smallEtaleTopology

/-- An étale `K(π, 1)` identification in dimension `d`: lisse étale cohomology of
`X` agrees with continuous group cohomology of geometric `π₁` as a
Frobenius-equivariant derived isomorphism `RΓ ≅ RH^0(π₁, M)`. The compactly
supported curve formula `RΓ_c ≅ LH_0(π₁, M(-1))[-2]` is the dimension-one
specialization from Proposition 64.29.3, not the definition at arbitrary
dimension. -/
class IsEtaleKPi1 : Prop where
  /-- Frobenius-equivariant derived identification `RΓ(X_k̄, F_ρ) ≅ RH^0(π₁, M)`. -/
  cohomology_eq :
    ∀ {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
      [HasWeakSheafify (smallEtale X) (ModuleCat.{u + 1} Λ)]
      [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
      [Abelian (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
      [Abelian (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
      [HasDerivedCategory.{u + 2}
        (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
      [HasDerivedCategory.{u + 2}
        (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
      [∀ U : X.left.Etale,
        HasWeakSheafify ((smallEtale X).over U) (ModuleCat.{u + 1} Λ)]
      [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
        (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
      [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
        (smallEtalePullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
      [∀ P : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
        (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
      [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
        (smallEtalePullback
            (geometricFrobeniusBaseChange X ≫
              FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
      [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
        (smallEtalePullback
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
              geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
      [HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          (actionInvariantsFunctor Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G))
        (HomologicalComplex.quasiIso
          (Action (ModuleCat.{u + 1} Λ) (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G)
          (ComplexShape.up ℤ))]
      (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
      (hM : Module.Finite Λ M.obj.V),
        ∃ e :
          geometricRGamma X (pi1ModuleDerived X etaBar M hM) ≅
            derivedInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M,
          e.hom ≫
              frobeniusEndInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M =
            geometricFrobeniusRGamma X (pi1ModuleDerived X etaBar M hM) ≫ e.hom

/-- Constructor packaging the étale `K(π, 1)` cohomology identification. -/
theorem IsEtaleKPi1.mk'
    (hcoh :
      ∀ {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
        [HasWeakSheafify (smallEtale X) (ModuleCat.{u + 1} Λ)]
        [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
        [Abelian (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
        [Abelian (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
        [HasDerivedCategory.{u + 2}
          (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
        [HasDerivedCategory.{u + 2}
          (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
          [∀ U : X.left.Etale,
          HasWeakSheafify ((smallEtale X).over U) (ModuleCat.{u + 1} Λ)]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
        [∀ P : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (geometricFrobeniusBaseChange X ≫
                FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
                geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
        [HasRightDerivedFunctor
          (RightDerived.Cochain.toDerived
            (actionInvariantsFunctor Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G))
          (HomologicalComplex.quasiIso
            (Action (ModuleCat.{u + 1} Λ) (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G)
            (ComplexShape.up ℤ))]
        (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
        (hM : Module.Finite Λ M.obj.V),
          ∃ e :
            geometricRGamma X (pi1ModuleDerived X etaBar M hM) ≅
              derivedInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M,
            e.hom ≫
                frobeniusEndInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M =
              geometricFrobeniusRGamma X (pi1ModuleDerived X etaBar M hM) ≫ e.hom) :
    IsEtaleKPi1 X etaBar :=
  sorry

/-- The étale `K(π, 1)` property unfolds as the Frobenius-equivariant derived
identification of geometric cohomology with derived geometric `π₁`-invariants. -/
theorem IsEtaleKPi1.spec :
    IsEtaleKPi1 X etaBar ↔
      ∀ {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
        [HasWeakSheafify (smallEtale X) (ModuleCat.{u + 1} Λ)]
        [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
        [Abelian (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
        [Abelian (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
        [HasDerivedCategory.{u + 2}
          (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
        [HasDerivedCategory.{u + 2}
          (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
          [∀ U : X.left.Etale,
          HasWeakSheafify ((smallEtale X).over U) (ModuleCat.{u + 1} Λ)]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
        [∀ P : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (geometricFrobeniusBaseChange X ≫
                FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
        [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
          (smallEtalePullback
              (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
                geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
        [HasRightDerivedFunctor
          (RightDerived.Cochain.toDerived
            (actionInvariantsFunctor Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G))
          (HomologicalComplex.quasiIso
            (Action (ModuleCat.{u + 1} Λ) (DegreeExtension.ofEtaleFundamentalGroup X etaBar).G)
            (ComplexShape.up ℤ))]
        (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
        (hM : Module.Finite Λ M.obj.V),
          ∃ e :
            geometricRGamma X (pi1ModuleDerived X etaBar M hM) ≅
              derivedInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M,
            e.hom ≫
                frobeniusEndInvariants (DegreeExtension.ofEtaleFundamentalGroup X etaBar) M =
              geometricFrobeniusRGamma X (pi1ModuleDerived X etaBar M hM) ≫ e.hom :=
  sorry

/-- Smooth geometrically irreducible curves that are not `P¹` are étale `K(π, 1)`, by
Proposition 64.29.3. -/
instance isEtaleKPi1_curve [Curve X] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1)] :
    IsEtaleKPi1 X etaBar :=
  sorry

/-- Remark 64.30.1 (1). If modeling projective curves then we can use cohomology
and we don't need the factor `q^n`: the conjugacy-class side equals
`Tr(π^{*n} | RΓ(X_k̄, F_ρ))`, with no extra `q^n`. -/
@[stacks 03VP]
theorem trace_eq_geometricRGamma [Curve X] [Projective X.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (h_ne_P1 :
      IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X etaBar))
    (hT : IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X etaBar) T)
    (hq : T.q = Fintype.card k)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    [HasWeakSheafify (smallEtale X) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [Abelian (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
    [Abelian (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory.{u + 2}
      (Sheaf (smallEtale X) (ModuleCat.{u + 1} Λ))]
    [HasDerivedCategory.{u + 2}
      (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]
    [∀ U : X.left.Etale,
      HasWeakSheafify ((smallEtale X).over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback (geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
    [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
    [∀ P : (geometricBaseChange X).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback (geometricFrobeniusBaseChange X)).op.HasLeftKanExtension P]
    [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback
          (geometricFrobeniusBaseChange X ≫
            FieldExtension.toSource k (AlgebraicClosure k) X.hom)).op.HasLeftKanExtension P]
    [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom ≫
            geometricFrobenius_ofFiniteField X)).op.HasLeftKanExtension P]
    (hunit : IsUnit (T.q : Λ))
    (M : DiscreteModuleCat Λ (DegreeExtension.ofEtaleFundamentalGroup X etaBar).middle)
    (hM : Module.Finite Λ M.obj.V) [Module.Projective Λ M.obj.V]
    (n : ℕ) (hn : 0 < n) :
    T.leftHandSum M n =
      (isPerfect_geometricRGamma X etaBar M hM).traceNatural
        (geometricFrobeniusRGamma X (pi1ModuleDerived X etaBar M hM) ^ n) :=
  sorry

/-- Remark 64.30.1 (2). The known examples are `Γ = π₁(X, η̄)` for `X` smooth,
geometrically irreducible, and an étale `K(π, 1)` over a finite field, with
`q = (#k)^{dim X}`. -/
@[stacks 03VP]
theorem hasAbstractTraceFormula_etaleFundamentalGroup
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsEtaleKPi1 X etaBar] :
    ∃ (d : ℕ) (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X etaBar)),
      topologicalKrullDim X.left = (d : WithBot ℕ∞) ∧
        T.q = Fintype.card k ^ d ∧
          IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X etaBar) T :=
  sorry

/-- On a smooth geometrically irreducible curve that is not `P¹`, the abstract
trace formula holds with `q = #k`, using the curve `K(π, 1)` identifications of
Proposition 64.29.3. -/
theorem hasAbstractTraceFormula_etaleFundamentalGroup_curve
    [Curve X] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (h_ne_P1 :
      IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1)) :
    ∃ T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X etaBar),
      T.q = Fintype.card k ∧
        IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X etaBar) T :=
  sorry

end AlgebraicGeometry.SchemeOverField

/-- Remark 64.30.1 (3). Given the integer `q` then the sets `S_d` are uniquely
determined. -/
@[stacks 03VP]
theorem ProfiniteGrp.multiplicity_unique
    {S : DegreeExtension.{u}} {T₁ T₂ : AbstractTraceData S}
    (h₁ : IsAbstractTraceFormula S T₁) (h₂ : IsAbstractTraceFormula S T₂)
    (hq : T₁.q = T₂.q) : T₁.multiplicity = T₂.multiplicity :=
  sorry
