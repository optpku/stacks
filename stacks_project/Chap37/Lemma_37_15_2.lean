module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.BaseChange
public import stacks_project.Chap37.Theorem_37_15_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.15.2 (1): relative flatness of a quasi-coherent module at a point is preserved
under pullback in a cartesian square of schemes. -/
@[stacks 047C]
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_pullback_of_isPullback :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
      (f : X ⟶ S) (g : S' ⟶ S), IsPullback g' f' f g →
      ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X'),
        flatOverAt ℱ f (g' x') →
          flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x')

/- Lemma 37.15.2 (2): in a cartesian square, relative flatness of a quasi-coherent module
is reflected at a point when the base morphism is flat at its image. -/
@[stacks 047C]
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_of_isPullback_of_flatAt_base :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
      (f : X ⟶ S) (g : S' ⟶ S), IsPullback g' f' f g →
      ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X'),
        Scheme.Hom.flatAt g (f' x') →
          flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x' →
            flatOverAt ℱ f (g' x'))

/- Lemma 37.15.2 (3): for a finitely presented module over a locally finitely presented
morphism, the open relative-flatness locus commutes with flat base change. -/
@[stacks 047C]
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_open_eq_preimage_of_isPullback_of_flat_base :
    ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
      (f : X ⟶ S) (g : S' ⟶ S), IsPullback g' f' f g →
      ∀ [Flat g] [LocallyOfFinitePresentation f]
        (ℱ : X.Modules) [ℱ.IsFinitePresentation] (W : X.Opens) (W' : X'.Opens),
        (W : Set X) = {x : X | flatOverAt ℱ f x} →
          (W' : Set X') =
              {x' : X' | flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x'} →
            W' = g' ⁻¹ᵁ W)

end AlgebraicGeometry.Scheme.Modules
