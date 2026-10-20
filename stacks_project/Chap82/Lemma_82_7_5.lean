module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact.LocallyFinite
import StacksCheckRecall

/-!
# Closures of images of locally finite closed families

In the good setup of Situation 82.2.1, a quasi-compact morphism over `B` sends a
locally finite family of closed subsets of the source point space to a locally
finite family of closures of images in the target point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u v

/- Lemma 82.7.5: In Situation 82.2.1, `S` is a scheme and `B` is a quasi-separated,
locally Noetherian, universally catenary algebraic space over `S`, equipped with a
dimension function `δ : Points B → ℤ`. Let `X, Y / B` be good: their structure morphisms
`pX : X ⟶ B` and `pY : Y ⟶ B` are quasi-separated and locally of finite type. Let
`f : X ⟶ Y` be a morphism over `B`, so `f ≫ pY = pX`. If `f` is quasi-compact and
`T` is a locally finite family of closed subsets of `Points X`, the closures of their
images form a locally finite family of closed subsets of `Points Y`.

The checked theorem holds for any quasi-compact morphism of algebraic spaces over a
scheme, so it implies this specialization without the additional base and goodness
assumptions. Each resulting subset is closed because it is a closure. -/
@[stacks 0ENZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFinite_closure_image :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f]
      {I : Type v} (T : I → Closeds (Points X)),
      LocallyFinite (fun i ↦ (T i : Set (Points X))) →
        LocallyFinite (fun i ↦ closure (Points.map f '' (T i : Set (Points X)))))
