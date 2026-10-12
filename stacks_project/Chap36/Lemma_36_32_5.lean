/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

/- Lemma 36.32.5 (1): if the canonical map from every residue field to the global
sections of the corresponding fiber is bijective, then the canonical map
`𝒪_S ⟶ f_*𝒪_X` is an isomorphism. -/
@[stacks 0E62] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (hΓ : ∀ s : S, Function.Bijective
        (Scheme.Hom.globalSectionsMap (f.fiberToSpecResidueField s))),
      IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 36.32.5 (2): the canonical structure-sheaf pushforward map remains an
isomorphism after every base change. -/
@[stacks 0E62] #check
  (AlgebraicGeometry.Scheme.Hom.baseChange_structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (hΓ : ∀ s : S, Function.Bijective
        (Scheme.Hom.globalSectionsMap (f.fiberToSpecResidueField s)))
      (g : S' ⟶ S),
      IsIso
        (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom))

/- Lemma 36.32.5 (3): locally on the base, `Rf_*𝒪_X` is the biproduct of the
degree-zero structure sheaf and a perfect complex of Tor amplitude in `[1, ∞)`. -/
@[stacks 0E62] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_local_structureSheafPushforward_decomposition :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (hΓ : ∀ s : S, Function.Bijective
        (Scheme.Hom.globalSectionsMap (f.fiberToSpecResidueField s)))
      (s : S),
      ∃ U : S.Opens, s ∈ U ∧
        ∃ P : RingedSpace.moduleDerivedOnOpen S.toRingedSpace U,
          RingedSpace.ModuleDerived.IsPerfect P ∧
            RingedSpace.HasTorAmplitudeGE P 1 ∧
              IsIsomorphic
                ((RingedSpace.moduleRestrictionToOpenDerived S.toRingedSpace U).obj
                  ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
                    ((DerivedCategory.singleFunctor X.Modules 0).obj
                      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))))
                (((DerivedCategory.singleFunctor
                    (RingedSpace.Modules
                      (S.toRingedSpace.restrict U.isOpenEmbedding)) 0).obj
                      (SheafOfModules.unit
                        (RingedSpace.ringCatSheaf
                          (S.toRingedSpace.restrict U.isOpenEmbedding)))) ⊞ P))
