module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

/-!
# Base change of relatively flat modules on algebraic spaces

Relative flatness of a quasi-coherent module is preserved by base change and is reflected
at a point when the base morphism is flat at the corresponding image point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A module on an algebraic space is flat at a point over a target if an étale scheme
square has relatively flat restriction at a point mapping to the given point. -/
def flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
    Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
      Scheme.Modules.flatOverAt
        ((restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj F) sq.map.left u

/-- A module on an algebraic space is flat over a target if it is relatively flat at every
point of the source. -/
def flatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y) : Prop :=
  ∀ x : Points X, flatOverAt F f x

/-- Pointwise relative flatness unpacks as the existence of an étale scheme presentation whose
restricted module is relatively flat at a germ mapping to the given point. -/
theorem flatOverAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X) :
    flatOverAt F f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
        (ha : Etale a) (hb : Etale b),
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Modules.flatOverAt
              ((@restrictFunctor S (ofOver U) X a ha ⋙ restrictToScheme U).obj F) h.left u := by
  constructor
  · rintro ⟨sq, u, hx, hflat⟩
    exact ⟨sq.left.left, sq.right.left, sq.left.hom, sq.right.hom, sq.map, u,
      sq.left.prop, sq.right.prop, sq.w, hx, hflat⟩
  · rintro ⟨U, V, a, b, h, u, ha, hb, hw, hx, hflat⟩
    exact ⟨⟨smallEtaleSite.mk a ha, smallEtaleSite.mk b hb, h, hw⟩, u, hx, hflat⟩

/-- Global relative flatness is the pointwise condition at every point of the source. -/
theorem flatOver_iff_forall_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) :
    flatOver F f ↔ ∀ x : Points X, flatOverAt F f x :=
  Iff.rfl

/-- In a cartesian square of algebraic spaces, relative flatness of a quasi-coherent module
at a point is preserved by pullback. -/
theorem flatOverAt_pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (x' : Points X')
    (hflat : flatOverAt F f (Points.map g' x')) :
    flatOverAt ((pullback g').obj F) f' x' :=
  sorry

/-- In a cartesian square of algebraic spaces, relative flatness of a quasi-coherent module
at a point is reflected when the base morphism is flat at the corresponding image point. -/
theorem flatOverAt_of_isPullback_of_flatAt_base {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (x' : Points X')
    (hbase : FlatAt g (Points.map f' x'))
    (hflat : flatOverAt ((pullback g').obj F) f' x') :
    flatOverAt F f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces, global relative flatness of a quasi-coherent
module is preserved by pullback. -/
theorem flatOver_pullback_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : flatOver F f) :
    flatOver ((pullback g').obj F) f' :=
  fun x' => flatOverAt_pullback_of_isPullback g' f' f g hcart F x'
    (hflat (Points.map g' x'))

end AlgebraicGeometry.AlgebraicSpace.Modules
