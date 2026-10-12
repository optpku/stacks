/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative.UpperShriekComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.UpperShriekAssignment.existsRelativeDualizingSheaf :
  ∀ {S : Scheme} [IsNoetherian S] (E : AlgebraicGeometry.Scheme.UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] → [IsSeparated f.hom.left] →
    ∃ W : RelativeDualizingSheaf f.hom.left,
      W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
        (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.UpperShriekAssignment.affineRelativeDualizingIso :
  ∀ {S : Scheme} [IsNoetherian S] (E : AlgebraicGeometry.Scheme.UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] → [IsSeparated f.hom.left] →
    (W : RelativeDualizingSheaf f.hom.left) →
    (hW : W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0) →
    (U : Scheme.affineOpens X.obj.left) → (V : Scheme.affineOpens Y.obj.left) →
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) →
    (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).obj
        (RingedSpace.ModuleDerived.cohomologySheaf
          (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0) ≅
      (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f.hom.left U V hVU))

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.UpperShriekAssignment.affineRelativeDualizingIso_naturality :
  ∀ {S : Scheme} [IsNoetherian S] (E : AlgebraicGeometry.Scheme.UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] → [IsSeparated f.hom.left] →
    (W : RelativeDualizingSheaf f.hom.left) →
    (hW : W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0) →
    (U U' : Scheme.affineOpens X.obj.left) → (hU : U' ≤ U) →
    (V V' : Scheme.affineOpens Y.obj.left) → (hV : V' ≤ V) →
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) → (hVU' : V' ≤ f.hom.left ⁻¹ᵁ U') →
    (s : Γ(RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0, V)) →
    RelativeDualizingSheaf.transition f.hom.left W U U' hU V V' hV hVU hVU'
        ((E.affineRelativeDualizingIso f W hW U V hVU).hom s) =
      (E.affineRelativeDualizingIso f W hW U' V' hVU').hom
        (restrictSections
          (RingedSpace.ModuleDerived.cohomologySheaf
            (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)
          V V' hV s))

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.UpperShriekAssignment.existsUniqueCompatibleRelativeDualizingIso :
  ∀ {S : Scheme} [IsNoetherian S] (E : AlgebraicGeometry.Scheme.UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] → [IsSeparated f.hom.left] →
    (W₀ : RelativeDualizingSheaf f.hom.left) →
    (hW₀ : W₀.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0) →
    (W : RelativeDualizingSheaf f.hom.left) →
    ∃! i : RingedSpace.ModuleDerived.cohomologySheaf
        (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0 ≅ W.module.obj,
      RelativeDualizingSheaf.Compatible f.hom.left W₀ W (eqToIso hW₀ ≪≫ i))

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.affineRelativeDualizingIso :
  ∀ {S : Scheme} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {omegaS : RingedSpace.ModuleDerived S.toRingedSpace}
    {homegaS : omegaS.IsDualizingComplex H}
    (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] →
    (W : RelativeDualizingSheaf f.hom.left) →
    (hW : W.module.obj = D.dualizingModule f) →
    (U : Scheme.affineOpens X.obj.left) → (V : Scheme.affineOpens Y.obj.left) →
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) →
    (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).obj
        (D.dualizingModule f) ≅
      (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f.hom.left U V hVU))

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.affineRelativeDualizingIso_naturality :
  ∀ {S : Scheme} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {omegaS : RingedSpace.ModuleDerived S.toRingedSpace}
    {homegaS : omegaS.IsDualizingComplex H}
    (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] →
    (W : RelativeDualizingSheaf f.hom.left) →
    (hW : W.module.obj = D.dualizingModule f) →
    (U U' : Scheme.affineOpens X.obj.left) → (hU : U' ≤ U) →
    (V V' : Scheme.affineOpens Y.obj.left) → (hV : V' ≤ V) →
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) → (hVU' : V' ≤ f.hom.left ⁻¹ᵁ U') →
    (s : Γ(D.dualizingModule f, V)) →
    RelativeDualizingSheaf.transition f.hom.left W U U' hU V V' hV hVU hVU'
        ((D.affineRelativeDualizingIso f W hW U V hVU).hom s) =
      (D.affineRelativeDualizingIso f W hW U' V' hVU').hom
        (restrictSections (D.dualizingModule f) V V' hV s))

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.existsRelativeDualizingSheaf :
  ∀ {S : Scheme} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {omegaS : RingedSpace.ModuleDerived S.toRingedSpace}
    {homegaS : omegaS.IsDualizingComplex H}
    (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] →
    ∃ W : RelativeDualizingSheaf f.hom.left, W.module.obj = D.dualizingModule f)

/- Lemma 49.15.1 -/
@[stacks 0BUL] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.existsUniqueCompatibleRelativeDualizingIso :
  ∀ {S : Scheme} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {omegaS : RingedSpace.ModuleDerived S.toRingedSpace}
    {homegaS : omegaS.IsDualizingComplex H}
    (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X),
    [Scheme.Hom.QuasiFinite f.hom.left] →
    (W₀ : RelativeDualizingSheaf f.hom.left) →
    (hW₀ : W₀.module.obj = D.dualizingModule f) →
    (W : RelativeDualizingSheaf f.hom.left) →
    ∃! i : D.dualizingModule f ≅ W.module.obj,
      RelativeDualizingSheaf.Compatible f.hom.left W₀ W (eqToIso hW₀ ≪≫ i))
