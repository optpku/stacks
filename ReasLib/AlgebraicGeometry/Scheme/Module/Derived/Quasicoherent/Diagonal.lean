/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]

/-- The diagonal Tor comparison for coherent modules on a regular variety. -/
theorem torDiagonal_isomorphic (F G : X.left.Modules)
    [F.IsCoherent] [G.IsCoherent]
    [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
    [RingedSpace.ModuleDerived.Tensor.Has
      (Limits.pullback X.hom X.hom).toRingedSpace] (i : ℕ) :
    IsIsomorphic
      (RingedSpace.ModuleDerived.tor i
        ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
          (SheafOfModules.unit X.left.ringCatSheaf))
        (Scheme.Modules.externalTensorProduct X.hom X.hom F G))
      ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
        (RingedSpace.ModuleDerived.tor i F G)) := sorry

/-- Derived pullback along the diagonal identifies an exterior tensor with the tensor on the
   diagonal. -/
theorem pullbackDiagonalTensor_isomorphic (K M : Scheme.DerivedQCoh X.left) :
    IsIsomorphic
      ((Scheme.DerivedQCoh.pullback (pullback.diagonal X.hom)).obj
        (Scheme.DerivedQCoh.tensorObj
          ((Scheme.DerivedQCoh.pullback (pullback.fst X.hom X.hom)).obj K)
          ((Scheme.DerivedQCoh.pullback (pullback.snd X.hom X.hom)).obj M)))
      (Scheme.DerivedQCoh.tensorObj K M) := sorry

/-- Tensoring the diagonal structure sheaf with an exterior tensor is the diagonal pushforward
   of the tensor on the diagonal. -/
theorem diagonalStructureSheafTensor_isomorphic (K M : Scheme.DerivedQCoh X.left) :
    IsIsomorphic
      (Scheme.DerivedQCoh.tensorObj
        (Scheme.DerivedQCoh.pushforwardStructureSheaf (pullback.diagonal X.hom))
        (Scheme.DerivedQCoh.tensorObj
          ((Scheme.DerivedQCoh.pullback (pullback.fst X.hom X.hom)).obj K)
          ((Scheme.DerivedQCoh.pullback (pullback.snd X.hom X.hom)).obj M)))
      ((Scheme.DerivedQCoh.pushforwardCohomologyIn (pullback.diagonal X.hom)).obj
        (Scheme.DerivedQCoh.tensorObj K M)) := sorry

end AlgebraicGeometry.SchemeOverField
