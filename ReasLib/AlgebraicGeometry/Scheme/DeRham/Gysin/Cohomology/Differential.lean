/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.HodgeCup
public import ReasLib.Topology.Sheaf.Cohomology.ClosedEmbedding

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules.RingedSite.ExteriorPower
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- The map on Hodge cohomology induced by the relative de Rham differential. -/
noncomputable def hodgeDifferential (f : X ⟶ S) (p q : ℕ) :
    hodgeCohomologyObject f p (q : ℤ) ⟶
      hodgeCohomologyObject f (p + 1) (q : ℤ) :=
  (DerivedCategory.homologyFunctor (coefficientModules f) (q : ℤ)).map
    ((globalDerivedFunctor f).map
      ((CochainComplex.singleFunctor
        (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) (0 : ℤ)).map
          (RingedSpace.DeRham.d f.toLRSHom.toShHom p)))

/-- `hodgeDifferential` is obtained by applying derived global sections and degree-`q`
homology to the single-complex map induced by the relative de Rham differential. -/
theorem hodgeDifferential_spec (f : X ⟶ S) (p q : ℕ) :
    hodgeDifferential f p q =
      (DerivedCategory.homologyFunctor (coefficientModules f) (q : ℤ)).map
        ((globalDerivedFunctor f).map
          ((CochainComplex.singleFunctor
            (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) (0 : ℤ)).map
              (RingedSpace.DeRham.d f.toLRSHom.toShHom p))) := sorry

namespace Gysin

variable {Z : Scheme.{u}}

/-- The definitional comparison between module pushforward followed by forgetting scalars and
additive-sheaf pushforward. -/
noncomputable def pushforwardUnderlyingIso (i : Z ⟶ X) :
    (RingedSpace.opensRingedSiteHom i.toShHom).modulePushforward ⋙
        RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite X.toRingedSpace) ≅
      RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite Z.toRingedSpace) ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat i.base :=
  Iso.refl _

/-- The forward map of `pushforwardUnderlyingIso` is the identity under the definitional
identification of its two functors. -/
theorem pushforwardUnderlyingIso_hom (i : Z ⟶ X) :
    (pushforwardUnderlyingIso i).hom = 𝟙 _ := sorry

/-- The canonical identification of global sheaf cohomology with cohomology on the terminal
open subset. -/
noncomputable def cohomologyTerminalEvaluationIso (Y : Scheme.{u})
    (F : Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) (q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{u} F q) ≅ F.H' q (⊤ : Opens Y) :=
  ((SiteAbelianSectionsDerived.HPrime.terminalIso
    (Opens.grothendieckTopology Y.carrier) ⊤ isTerminalTop q).app F).symm ≪≫
  eqToIso (Sheaf.cohomologyAtObjectFunctor_obj
    (Opens.grothendieckTopology Y.carrier) ⊤ q F)

/-- The forward terminal-evaluation map is the inverse terminal comparison followed by the
evaluation identification with `F.H' q ⊤`. -/
theorem cohomologyTerminalEvaluationIso_hom (Y : Scheme.{u})
    (F : Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) (q : ℕ) :
    (cohomologyTerminalEvaluationIso Y F q).hom =
      ((SiteAbelianSectionsDerived.HPrime.terminalIso
        (Opens.grothendieckTopology Y.carrier) ⊤ isTerminalTop q).app F).inv ≫
        eqToHom (Sheaf.cohomologyAtObjectFunctor_obj
          (Opens.grothendieckTopology Y.carrier) ⊤ q F) := sorry

/-- The shifted source model of the cohomological Gysin map is canonically the underlying
additive group of Hodge cohomology on the closed subscheme. -/
noncomputable def hodgeSourceModelIso
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S) (p q c : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))))) ≅
      (forget₂ (ModuleCat (coefficientRing (i ≫ f))) AddCommGrpCat).obj
        (hodgeCohomologyObject (i ≫ f) p (q : ℤ)) :=
  hodgeRestrictionSourceIso i f p q c ≪≫
    moduleCohomologyTerminalIso X.toRingedSpace
      ((Scheme.Modules.toRingedSpace X).obj
        ((Scheme.Modules.pushforward i).obj
          (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q ≪≫
    (Sheaf.functorH (Opens.grothendieckTopology X.carrier) q).mapIso
      ((pushforwardUnderlyingIso i).app
        ((Scheme.Modules.toRingedSpace Z).obj
          (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) ≪≫
    cohomologyTerminalEvaluationIso X
      ((TopCat.Sheaf.pushforward AddCommGrpCat i.base).obj
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))) q ≪≫
    (@asIso _ _ _ _
      (CategoryTheory.Sheaf.pushforwardCohomologyMap i.base
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q (⊤ : Opens X))
      (CategoryTheory.Sheaf.ClosedEmbedding.comparison_isIso i.base
        (IsClosedImmersion.isClosedEmbedding i)
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q (⊤ : Opens X))) ≪≫
    eqToIso (congrArg
      (fun U : Opens Z ↦
        ((RingedSite.Hom.underlyingAbelianSheafFunctor
          (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))).H' q U)
      (Opens.map_top i.base)) ≪≫
    (cohomologyTerminalEvaluationIso Z
      ((RingedSite.Hom.underlyingAbelianSheafFunctor
        (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
          ((Scheme.Modules.toRingedSpace Z).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q).symm ≪≫
    (moduleCohomologyTerminalIso Z.toRingedSpace
      ((Scheme.Modules.toRingedSpace Z).obj
        (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)) q).symm ≪≫
    (hodgeOrdinaryCohomologyIso (i ≫ f) p q).symm

/-- The forward source-model comparison is the composite through pushforward cohomology,
closed-embedding comparison, and ordinary Hodge cohomology on `Z`. -/
theorem hodgeSourceModelIso_hom
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S) (p q c : ℕ) :
    (hodgeSourceModelIso i f p q c).hom =
      (hodgeRestrictionSourceIso i f p q c).hom ≫
        (moduleCohomologyTerminalIso X.toRingedSpace
          ((Scheme.Modules.toRingedSpace X).obj
            ((Scheme.Modules.pushforward i).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q).hom ≫
        ((Sheaf.functorH (Opens.grothendieckTopology X.carrier) q).mapIso
          ((pushforwardUnderlyingIso i).app
            ((Scheme.Modules.toRingedSpace Z).obj
              (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))).hom ≫
        (cohomologyTerminalEvaluationIso X
          ((TopCat.Sheaf.pushforward AddCommGrpCat i.base).obj
            ((RingedSite.Hom.underlyingAbelianSheafFunctor
              (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))) q).hom ≫
        CategoryTheory.Sheaf.pushforwardCohomologyMap i.base
          ((RingedSite.Hom.underlyingAbelianSheafFunctor
            (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
              ((Scheme.Modules.toRingedSpace Z).obj
                (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q (⊤ : Opens X) ≫
        eqToHom (congrArg
          (fun U : Opens Z ↦
            ((RingedSite.Hom.underlyingAbelianSheafFunctor
              (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))).H' q U)
          (Opens.map_top i.base)) ≫
        (cohomologyTerminalEvaluationIso Z
          ((RingedSite.Hom.underlyingAbelianSheafFunctor
            (RingedSpace.opensRingedSite Z.toRingedSpace)).obj
              ((Scheme.Modules.toRingedSpace Z).obj
                (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q).inv ≫
        (moduleCohomologyTerminalIso Z.toRingedSpace
          ((Scheme.Modules.toRingedSpace Z).obj
            (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)) q).inv ≫
        (hodgeOrdinaryCohomologyIso (i ≫ f) p q).inv := sorry

/-- The de Rham differential on the shifted source models used by the cohomological Gysin
maps, transported from canonical Hodge cohomology on `Z`. -/
noncomputable def hodgeSourceDifferential
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S) (p q c : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p)))))) ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.moduleSectionsRestrictionDerived i.toShHom ⊤).obj
            ((RingedSpace.Module.Derived.GlobalSections.functor Z.toRingedSpace).obj
              ((DerivedCategory.singleFunctor Z.toRingedSpace.Modules (c : ℤ)).obj
                ((Scheme.Modules.toRingedSpace Z).obj
                  (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] (p + 1))))))) :=
  (hodgeSourceModelIso i f p q c).hom ≫
    (forget₂ (ModuleCat (coefficientRing (i ≫ f))) AddCommGrpCat).map
      (hodgeDifferential (i ≫ f) p q) ≫
    (hodgeSourceModelIso i f (p + 1) q c).inv

/-- The source differential is conjugation of the canonical Hodge differential by the two
source-model comparisons. -/
theorem hodgeSourceDifferential_spec
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ S) (p q c : ℕ) :
    hodgeSourceDifferential i f p q c =
      (hodgeSourceModelIso i f p q c).hom ≫
        (forget₂ (ModuleCat (coefficientRing (i ≫ f))) AddCommGrpCat).map
          (hodgeDifferential (i ≫ f) p q) ≫
        (hodgeSourceModelIso i f (p + 1) q c).inv := sorry

/-- The de Rham differential on the target models used by the cohomological Gysin maps,
including the canonical transport from `(p + c) + 1` to `(p + 1) + c`. -/
noncomputable def hodgeTargetDifferential
    (f : X ⟶ S) (p q c : ℕ) :
    (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
      AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj (relativeFormQCoh f (p + c)))))) ⟶
      (forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat).obj
        ((DerivedCategory.homologyFunctor
          (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
            (q + c : ℤ)).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
            ((ModuleCech.moduleToDerived X).obj
              ((Scheme.QCoh.inclusion X).obj
                (relativeFormQCoh f ((p + 1) + c)))))) :=
  (hodgeModelIso f (p + c) (q + c)).hom ≫
    (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).map
      (hodgeDifferential f (p + c) (q + c)) ≫
    eqToHom (congrArg
      (fun n : ℕ ↦ (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
        (hodgeCohomologyObject f n ((q + c : ℕ) : ℤ)))
      (Nat.add_right_comm p 1 c).symm) ≫
    (hodgeModelIso f ((p + 1) + c) (q + c)).inv

/-- The target differential is the canonical Hodge differential conjugated by the Hodge-model
comparisons and the degree transport `(p + c) + 1 = (p + 1) + c`. -/
theorem hodgeTargetDifferential_spec
    (f : X ⟶ S) (p q c : ℕ) :
    hodgeTargetDifferential f p q c =
      (hodgeModelIso f (p + c) (q + c)).hom ≫
        (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).map
          (hodgeDifferential f (p + c) (q + c)) ≫
        eqToHom (congrArg
          (fun n : ℕ ↦ (forget₂ (ModuleCat (coefficientRing f)) AddCommGrpCat).obj
            (hodgeCohomologyObject f n ((q + c : ℕ) : ℤ)))
          (Nat.add_right_comm p 1 c).symm) ≫
        (hodgeModelIso f ((p + 1) + c) (q + c)).inv := sorry

/-- For a smooth morphism `f : X ⟶ S` and a finitely presented Koszul-regular closed
immersion `i : Z ⟶ X` whose conormal sheaf has rank `c`, the cohomological Gysin maps
commute with the relative de Rham differentials on Hodge cohomology. -/
theorem hodgeCohomologyMap_d {Z X S : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    (f : X ⟶ S) [Smooth f] [IsKoszulRegularImmersion i] (c p q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    CommSq
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat).map (hodgeCohomologyMapOfSmoothOfKoszulRegular i f p q c))
      (hodgeSourceDifferential i f p q c)
      (hodgeTargetDifferential f p q c)
      ((forget₂ (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace))
        AddCommGrpCat).map (hodgeCohomologyMapOfSmoothOfKoszulRegular i f (p + 1) q c)) :=
  sorry

end Gysin
end AlgebraicGeometry.Scheme.DeRham

end
