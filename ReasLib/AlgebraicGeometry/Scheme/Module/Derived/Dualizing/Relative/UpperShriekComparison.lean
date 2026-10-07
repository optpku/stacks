module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Pseudofunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Dualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.UpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]

/-- A quasi-finite separated upper-shriek morphism admits a relative dualizing sheaf
whose module is the degree-zero cohomology of the upper-shriek image of the structure sheaf. -/
theorem existsRelativeDualizingSheaf (E : UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X)
    [Scheme.Hom.QuasiFinite f.hom.left] [IsSeparated f.hom.left] :
    ∃ W : RelativeDualizingSheaf f.hom.left,
      W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
        (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0 := sorry

/-- The affine section comparison induced by a relative dualizing realization of upper shriek. -/
noncomputable def affineRelativeDualizingIso (E : UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X)
    [Scheme.Hom.QuasiFinite f.hom.left] [IsSeparated f.hom.left]
    (W : RelativeDualizingSheaf f.hom.left)
    (hW : W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)
    (U : Scheme.affineOpens X.obj.left) (V : Scheme.affineOpens Y.obj.left)
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) :
    (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).obj
        (RingedSpace.ModuleDerived.cohomologySheaf
          (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0) ≅
      (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f.hom.left U V hVU) :=
  (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).mapIso
      (eqToIso hW).symm ≪≫
    W.sectionIso U V hVU

/-- The affine upper-shriek comparison commutes with restriction of sections and relative
dualizing presentation transitions. -/
theorem affineRelativeDualizingIso_naturality (E : UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X)
    [Scheme.Hom.QuasiFinite f.hom.left] [IsSeparated f.hom.left]
    (W : RelativeDualizingSheaf f.hom.left)
    (hW : W.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)
    (U U' : Scheme.affineOpens X.obj.left) (hU : U' ≤ U)
    (V V' : Scheme.affineOpens Y.obj.left) (hV : V' ≤ V)
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) (hVU' : V' ≤ f.hom.left ⁻¹ᵁ U')
    (s : Γ(RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0, V)) :
    RelativeDualizingSheaf.transition f.hom.left W U U' hU V V' hV hVU hVU'
        ((E.affineRelativeDualizingIso f W hW U V hVU).hom s) =
      (E.affineRelativeDualizingIso f W hW U' V' hVU').hom
        (restrictSections
          (RingedSpace.ModuleDerived.cohomologySheaf
            (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)
          V V' hV s) := sorry

/-- A relative dualizing realization of upper shriek is uniquely compatible with every other
relative dualizing sheaf. -/
theorem existsUniqueCompatibleRelativeDualizingIso (E : UpperShriekAssignment S)
    {Y X : FiniteTypeSeparatedOver S} (f : Y ⟶ X)
    [Scheme.Hom.QuasiFinite f.hom.left] [IsSeparated f.hom.left]
    (W₀ : RelativeDualizingSheaf f.hom.left)
    (hW₀ : W₀.module.obj = RingedSpace.ModuleDerived.cohomologySheaf
      (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0)
    (W : RelativeDualizingSheaf f.hom.left) :
    ∃! i : RingedSpace.ModuleDerived.cohomologySheaf
        (((E.map f).obj (DerivedQCoh.structureSheafPlus X.obj.left)).obj.obj) 0 ≅ W.module.obj,
      RelativeDualizingSheaf.Compatible f.hom.left W₀ W (eqToIso hW₀ ≪≫ i) := sorry

end AlgebraicGeometry.Scheme.UpperShriekAssignment

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {omegaS : RingedSpace.ModuleDerived S.toRingedSpace}
variable {homegaS : omegaS.IsDualizingComplex H}

/-- A quasi-finite new upper-shriek morphism admits a relative dualizing sheaf whose module is
the degree-zero dualizing module. -/
theorem existsRelativeDualizingSheaf (D : NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X) [Scheme.Hom.QuasiFinite f.hom.left] :
    ∃ W : RelativeDualizingSheaf f.hom.left, W.module.obj = D.dualizingModule f := sorry

/-- The affine section comparison induced by a relative dualizing realization of new upper
shriek. -/
noncomputable def affineRelativeDualizingIso
    (D : NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X) [Scheme.Hom.QuasiFinite f.hom.left]
    (W : RelativeDualizingSheaf f.hom.left) (hW : W.module.obj = D.dualizingModule f)
    (U : Scheme.affineOpens X.obj.left) (V : Scheme.affineOpens Y.obj.left)
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) :
    (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).obj
        (D.dualizingModule f) ≅
      (W.presentation U V hVU).module
        (IsLocallyNoetherian.component_noetherian U)
        (IsLocallyNoetherian.component_noetherian V)
        (affineQuasiFinite f.hom.left U V hVU) :=
  (RingedSpace.moduleSectionsEvaluationFunctor (Y.obj.left).toRingedSpace V).mapIso
      (eqToIso hW).symm ≪≫
    W.sectionIso U V hVU

/-- The affine new-upper-shriek comparison commutes with restriction of sections and relative
dualizing presentation transitions. -/
theorem affineRelativeDualizingIso_naturality
    (D : NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X) [Scheme.Hom.QuasiFinite f.hom.left]
    (W : RelativeDualizingSheaf f.hom.left) (hW : W.module.obj = D.dualizingModule f)
    (U U' : Scheme.affineOpens X.obj.left) (hU : U' ≤ U)
    (V V' : Scheme.affineOpens Y.obj.left) (hV : V' ≤ V)
    (hVU : V ≤ f.hom.left ⁻¹ᵁ U) (hVU' : V' ≤ f.hom.left ⁻¹ᵁ U')
    (s : Γ(D.dualizingModule f, V)) :
    RelativeDualizingSheaf.transition f.hom.left W U U' hU V V' hV hVU hVU'
        ((D.affineRelativeDualizingIso f W hW U V hVU).hom s) =
      (D.affineRelativeDualizingIso f W hW U' V' hVU').hom
        (restrictSections (D.dualizingModule f) V V' hV s) := sorry

/-- A relative dualizing realization of new upper shriek is uniquely compatible with every
other relative dualizing sheaf. -/
theorem existsUniqueCompatibleRelativeDualizingIso
    (D : NewUpperShriekAssignment S H omegaS homegaS)
    {Y X : FiniteTypeOver S} (f : Y ⟶ X) [Scheme.Hom.QuasiFinite f.hom.left]
    (W₀ : RelativeDualizingSheaf f.hom.left) (hW₀ : W₀.module.obj = D.dualizingModule f)
    (W : RelativeDualizingSheaf f.hom.left) :
    ∃! i : D.dualizingModule f ≅ W.module.obj,
      RelativeDualizingSheaf.Compatible f.hom.left W₀ W (eqToIso hW₀ ≪≫ i) := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
