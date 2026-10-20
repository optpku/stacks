module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Proper support of modules

A module has proper support over a morphism if its support is contained in
a closed subspace proper over the target. For finite-type quasi-coherent
modules along locally-of-finite-type morphisms this is equivalent to properness
of the scheme-theoretic support.

Properness over the base of the closed support of a finite-type quasi-coherent
module is preserved by pullback in a cartesian square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- In a cartesian square of algebraic spaces, pullback preserves properness over
the base of the closed support of a finite-type quasi-coherent module. -/
theorem closedSupport_pullback_isProperOver {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : ClosedSubset.ProperOver f (closedSupport F)) :
    ClosedSubset.ProperOver f' (closedSupport ((pullback g').obj F)) :=
  sorry

/-- Properness of closed support over a base is preserved by inverse image along
the source projection of a chosen pullback. -/
theorem closedSupport_pullback_isProperOver_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : ClosedSubset.ProperOver f (closedSupport F)) :
    ClosedSubset.ProperOver (Limits.pullback.snd f g)
      (closedSupport ((pullback (Limits.pullback.fst f g)).obj F)) :=
  sorry

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A module on `X` has proper support over `f : X ⟶ Y` when some closed
subspace containing the étale-site support is proper over `Y`. -/
class HasProperSupportOver (f : X ⟶ Y) (F : X.Modules) : Prop where
  /-- Some closed subspace containing the support is proper over the base. -/
  exists_closedSubspace :
    ∃ Z : ClosedSubspace X, Proper (Z.ι ≫ f) ∧ moduleSupport F ⊆ Z.pointsSet

/-- Having proper support over `f` means some closed subspace containing the
module support is proper over `Y`. -/
theorem hasProperSupportOver_spec (f : X ⟶ Y) (F : X.Modules) :
    HasProperSupportOver f F ↔
      ∃ Z : ClosedSubspace X, Proper (Z.ι ≫ f) ∧ moduleSupport F ⊆ Z.pointsSet :=
  sorry

/-- If `f` is proper, then every module on `X` has proper support over `f`. -/
instance instHasProperSupportOver_of_proper (f : X ⟶ Y) [Proper f]
    (F : X.Modules) : HasProperSupportOver f F := sorry

/-- For a finite-type quasi-coherent module along a locally-of-finite-type
morphism, proper support is properness of the scheme-theoretic support over
the target. -/
theorem hasProperSupportOver_iff (f : X ⟶ Y) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    HasProperSupportOver f F ↔ Proper ((schemeTheoreticSupport F).ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
