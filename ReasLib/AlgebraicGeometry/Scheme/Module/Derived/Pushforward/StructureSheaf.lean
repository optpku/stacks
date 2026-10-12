/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Locally on the base, the derived pushforward of the structure sheaf is the biproduct
of the degree-zero structure sheaf and a perfect complex of Tor amplitude in `[1, ∞)`. -/
theorem exists_local_structureSheafPushforward_decomposition
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (hΓ : ∀ s : S, Function.Bijective
      (Scheme.Hom.globalSectionsMap (f.fiberToSpecResidueField s)))
    (s : S) :
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
                        (S.toRingedSpace.restrict U.isOpenEmbedding)))) ⊞ P) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived

namespace AlgebraicGeometry.Scheme.Hom

/-- If the canonical map from every residue field to the global sections of the
corresponding fiber is bijective, then `𝒪_S ⟶ f_*𝒪_X` is an isomorphism. -/
theorem structureSheafMap_isIso_of_fiberGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (hΓ : ∀ s : S,
      Function.Bijective (globalSectionsMap (f.fiberToSpecResidueField s))) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) := sorry

/-- Under the fiberwise global-sections hypothesis, the canonical structure-sheaf
pushforward map is an isomorphism after every base change. -/
theorem baseChange_structureSheafMap_isIso_of_fiberGlobalSections
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (hΓ : ∀ s : S,
      Function.Bijective (globalSectionsMap (f.fiberToSpecResidueField s)))
    (g : S' ⟶ S) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom) := sorry

namespace StructureSheaf

/-- A proper, flat, finitely presented morphism with geometrically reduced and geometrically
connected fibers has an invertible canonical structure-sheaf pushforward map. -/
@[instance]
theorem isIso_of_geometricallyReduced_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [GeometricallyReduced f] [GeometricallyConnected f] :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) := sorry

/-- After any base change of a proper, flat, finitely presented morphism with geometrically
reduced and geometrically connected fibers, the canonical structure-sheaf pushforward map
is invertible. -/
@[instance]
theorem baseChange_isIso_of_geometricallyReduced_geometricallyConnected
    {X S S' : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [GeometricallyReduced f] [GeometricallyConnected f] (g : S' ⟶ S) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap (pullback.snd f g).toShHom) := sorry

end StructureSheaf

end AlgebraicGeometry.Scheme.Hom
