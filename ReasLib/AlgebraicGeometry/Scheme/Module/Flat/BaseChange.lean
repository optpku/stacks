module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Transitivity

/-!
# Base change of relatively flat module sheaves on schemes

This module records preservation of relative flatness for a quasi-coherent module sheaf under
pullback along the first projection of a scheme pullback.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)

/-- Relative flatness at a point is preserved when a quasi-coherent module sheaf is pulled back
along the first projection of a scheme pullback. -/
theorem flatOverAt_pullback_fst
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (x' : (CategoryTheory.Limits.pullback f g : Scheme.{u}))
    (hflat : flatOverAt ℱ f ((CategoryTheory.Limits.pullback.fst f g).base x')) :
    flatOverAt ((Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f g)).obj ℱ)
      (CategoryTheory.Limits.pullback.snd f g) x' := sorry

/-- Relative flatness of a quasi-coherent module sheaf is preserved by pullback along the first
projection of a scheme pullback. -/
theorem flatOver_pullback_fst
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (hflat : flatOver ℱ f) :
    flatOver ((Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f g)).obj ℱ)
      (CategoryTheory.Limits.pullback.snd f g) := sorry

/-- Relative flatness of a quasicoherent module sheaf is preserved around a cartesian square of
schemes. -/
theorem isFlatOver_pullback_of_isPullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (sq : IsPullback g' f' f g)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] :
    SheafOfModules.IsFlatOver ((Scheme.Modules.pullback g').obj ℱ) f'.toShHom := sorry

/-- Relative flatness at a point is preserved by pulling a quasi-coherent module around a
cartesian square of schemes. -/
@[stacks 047C]
theorem flatOverAt_pullback_of_isPullback
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X')
    (hflat : flatOverAt ℱ f (g' x')) :
    flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x' := sorry

/-- Relative flatness at a point is reflected around a cartesian square when the base morphism
is flat at the corresponding point. -/
@[stacks 047C]
theorem flatOverAt_of_isPullback_of_flatAt_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (hcart : IsPullback g' f' f g)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (x' : X')
    (hbase : Scheme.Hom.flatAt g (f' x'))
    (hflat : flatOverAt ((Scheme.Modules.pullback g').obj ℱ) f' x') :
    flatOverAt ℱ f (g' x') := sorry

end AlgebraicGeometry.Scheme.Modules
