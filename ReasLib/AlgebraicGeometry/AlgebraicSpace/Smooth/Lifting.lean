module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Étale-local lifting for smooth morphisms of algebraic spaces

A smooth morphism of algebraic spaces has the right lifting property against
an arbitrary thickening after passage to an étale covering of the thickened
object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- The dotted arrow `U' ⟶ X` exists after base change of a solid square along
`π : U' ⟶ T'`, i.e. both triangles of the pulled-back diagram commute. -/
def LiftsAlong {S : Scheme.{u}} {X Y T T' U' : AlgebraicSpace S}
    (f : X ⟶ Y) (i : T ⟶ T') (a : T ⟶ X) (b : T' ⟶ Y) (π : U' ⟶ T') : Prop :=
  ∃ l : U' ⟶ X,
    pullback.snd i π ≫ l = pullback.fst i π ≫ a ∧ l ≫ f = π ≫ b

/-- `LiftsAlong` is existence of a map `U' ⟶ X` whose two triangles commute. -/
theorem liftsAlong_iff {S : Scheme.{u}} {X Y T T' U' : AlgebraicSpace S}
    (f : X ⟶ Y) (i : T ⟶ T') (a : T ⟶ X) (b : T' ⟶ Y) (π : U' ⟶ T') :
    LiftsAlong f i a b π ↔
      ∃ l : U' ⟶ X,
        pullback.snd i π ≫ l = pullback.fst i π ≫ a ∧ l ≫ f = π ≫ b :=
  sorry

/-- A morphism `l : U' ⟶ X` satisfying the two triangle identities is a lift
along `π`. -/
theorem liftsAlong_of_hom {S : Scheme.{u}} {X Y T T' U' : AlgebraicSpace S}
    (f : X ⟶ Y) (i : T ⟶ T') (a : T ⟶ X) (b : T' ⟶ Y) (π : U' ⟶ T')
    (l : U' ⟶ X) (hT : pullback.snd i π ≫ l = pullback.fst i π ≫ a)
    (hY : l ≫ f = π ≫ b) : LiftsAlong f i a b π :=
  sorry

/-- Base change of a solid commutative square along `π : U' ⟶ T'` remains a
commutative square. -/
theorem liftsAlongCommSq {S : Scheme.{u}} {X Y T T' U' : AlgebraicSpace S}
    {f : X ⟶ Y} {i : T ⟶ T'} {a : T ⟶ X} {b : T' ⟶ Y}
    (sq : CommSq a i f b) (π : U' ⟶ T') :
    CommSq (pullback.fst i π ≫ a) (pullback.snd i π) f (π ≫ b) :=
  sorry

/-- `LiftsAlong` is equivalent to `HasLift` of the pulled-back square. -/
theorem liftsAlong_iff_hasLift {S : Scheme.{u}} {X Y T T' U' : AlgebraicSpace S}
    (f : X ⟶ Y) (i : T ⟶ T') (a : T ⟶ X) (b : T' ⟶ Y)
    (sq : CommSq a i f b) (π : U' ⟶ T') :
    LiftsAlong f i a b π ↔ (liftsAlongCommSq sq π).HasLift :=
  sorry

/-- For a commutative square of algebraic
spaces over `S` with smooth `f : X ⟶ Y` and thickening `i : T ⟶ T'`, there
exists an étale covering `{T'ᵢ ⟶ T'}` such that each pulled-back square along
`T ×[T'] T'ᵢ` admits a dotted lift `T'ᵢ ⟶ X`. -/
@[stacks 0CHJ]
theorem exists_etaleCovering_lift {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] (i : T ⟶ T') [IsThickening i]
    (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b) :
    ∃ 𝒰 : etalePrecoverage.ZeroHypercover.{u} T',
      ∀ j : 𝒰.I₀, LiftsAlong f i a b (𝒰.f j) :=
  sorry

/-- Existence of an étale covering with lifts is equivalent to existence of a
`Type u` family of morphisms with lifts satisfying `EtaleCovering`. -/
theorem exists_etaleCovering_lift_spec {S : Scheme.{u}}
    {X Y T T' : AlgebraicSpace S} (f : X ⟶ Y) (i : T ⟶ T')
    (a : T ⟶ X) (b : T' ⟶ Y) :
    (∃ 𝒰 : etalePrecoverage.ZeroHypercover.{u} T',
        ∀ j : 𝒰.I₀, LiftsAlong f i a b (𝒰.f j)) ↔
      ∃ (ι : Type u) (T'ᵢ : ι → AlgebraicSpace S) (π : ∀ j, T'ᵢ j ⟶ T'),
        EtaleCovering (fun j ↦ Over.mk (π j)) ∧
          ∀ j, LiftsAlong f i a b (π j) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
