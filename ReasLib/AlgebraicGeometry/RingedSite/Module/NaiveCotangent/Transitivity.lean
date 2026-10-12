/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Transitivity
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.SixTerm
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity for naive cotangent complexes

A tower of commutative ring sheaves has three canonical naive cotangent complexes.  This file
packages the comparison with the mapping cocone at the level of an arbitrary ringed site; the
opens-site and ringed-space statements are specializations of this owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{u}}

/-- Extension of scalars of `NL(O₂/O₁)` along `O₂ ⟶ O₃`, viewed as a cochain complex of
`O₃`-module sheaves. -/
@[stacks 0E1Y "base-changed naive cotangent complex"]
noncomputable abbrev baseChange (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    CochainComplex (ringedSiteModuleCategory J O₃) ℤ :=
  (extendComplex alpha).obj (NaiveCotangent.obj O₁ (Under.mk phi))

/-- The transitivity datum for the tower `O₁ ⟶ O₂ ⟶ O₃`: a comparison of the two target
cotangent complexes and a map from the base-changed source complex to its mapping cocone, with
the homological properties that produce the Jacobi-Zariski six-term sequence. -/
@[stacks 0E1Y "transitivity datum"]
structure Transitivity (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) where
  /-- The comparison `NL(O₃/O₁) ⟶ NL(O₃/O₂)`. -/
  comparison : NaiveCotangent.obj O₁ (Under.mk (phi ≫ alpha)) ⟶
    NaiveCotangent.obj O₂ (Under.mk alpha)
  /-- The map from the base-changed source complex to the shifted cone of `comparison`. -/
  toCocone : baseChange phi alpha ⟶ CochainComplex.mappingCocone comparison
  /-- The transitivity map is an isomorphism on degree-zero homology. -/
  zeroIsIso : IsIso (HomologicalComplex.homologyMap toCocone 0)
  /-- The transitivity map is an epimorphism on degree-minus-one homology. -/
  negOneEpi : Epi (HomologicalComplex.homologyMap toCocone (-1))

/-- Lemma 17.31.5 (0E1Y): the canonical transitivity cocone map is an isomorphism on
degree-zero homology. -/
@[stacks 0E1Y "degree-zero naive-cotangent transitivity"]
instance toCocone_zero_isIso (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    IsIso (HomologicalComplex.homologyMap
      (Presentation.toCocone phi alpha) 0) := sorry

/-- Lemma 17.31.5 (0E1Y): the canonical transitivity cocone map is epic on
degree-minus-one homology. -/
@[stacks 0E1Y "degree-minus-one naive-cotangent transitivity"]
instance toCocone_negOne_epi (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Epi (HomologicalComplex.homologyMap
      (Presentation.toCocone phi alpha) (-1)) := sorry

/-- Lemma 17.31.5 (0E1Y): the degree-zero homology map of the canonical comparison is epic. -/
@[stacks 0E1Y "degree-zero comparison epimorphism"]
theorem comparison_zero_epi (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Epi (HomologicalComplex.homologyMap (Presentation.comparison phi alpha) 0) := sorry

namespace Transitivity

/-- The Jacobi-Zariski six-term homology segment attached to a naive-cotangent transitivity
datum. -/
@[stacks 0E1Y "naive cotangent six-term sequence"]
noncomputable def sixTerm {phi : O₁ ⟶ O₂} {alpha : O₂ ⟶ O₃}
    (t : Transitivity phi alpha) :
    ComposableArrows (ringedSiteModuleCategory J O₃) 5 :=
  CochainComplex.mappingCocone.sixTerm t.comparison t.toCocone t.zeroIsIso

/-- The Jacobi-Zariski six-term segment attached to a transitivity datum is exact. -/
@[stacks 0E1Y "exact naive-cotangent transitivity sequence"]
theorem sixTerm_exact {phi : O₁ ⟶ O₂} {alpha : O₂ ⟶ O₃}
    (t : Transitivity phi alpha) : t.sixTerm.Exact := sorry

/-- The final degree-zero comparison in the Jacobi-Zariski sequence is epic. -/
theorem comparison_zero_epi {phi : O₁ ⟶ O₂} {alpha : O₂ ⟶ O₃}
    (t : Transitivity phi alpha) :
    Epi (HomologicalComplex.homologyMap t.comparison 0) := sorry

end Transitivity

/-- Lemma 17.31.5 (0E1Y): the canonical transitivity datum for a tower of commutative ring
sheaves on a ringed site. -/
@[stacks 0E1Y "naive cotangent transitivity"]
noncomputable def transitivity (phi : O₁ ⟶ O₂) (alpha : O₂ ⟶ O₃) :
    Transitivity phi alpha where
  comparison := Presentation.comparison phi alpha
  toCocone := Presentation.toCocone phi alpha
  zeroIsIso := toCocone_zero_isIso phi alpha
  negOneEpi := toCocone_negOne_epi phi alpha

end SheafOfModules.RingedSite.NaiveCotangent
