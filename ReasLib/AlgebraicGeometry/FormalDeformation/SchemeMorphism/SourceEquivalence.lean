module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.Source
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage

/-!
# Equivalence of source deformation categories

A scheme morphism with an isomorphic structure-sheaf pushforward map and
vanishing first higher direct image induces an equivalence on source deformations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped BasedFunctor

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- If the canonical structure-sheaf pushforward map of a scheme morphism over a field is
an isomorphism and its first higher direct image vanishes, the source deformation functor
is an equivalence over the category of Artinian local algebras. -/
instance instIsEquivalence_sourceBasedFunctor
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [h_pushforward : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    [h_R1 : Fact
      (IsZero
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1))] :
    BasedFunctor.IsEquivalence (sourceBasedFunctor Λ k X Y f hX hY hf) :=
  sorry

end FlatSchemeMorphismCat
