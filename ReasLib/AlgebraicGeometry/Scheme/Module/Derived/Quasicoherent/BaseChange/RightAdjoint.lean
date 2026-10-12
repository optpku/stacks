/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange

public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange

variable {X' X Y' Y : Scheme.{u}}

/-- The right-adjoint mate of the canonical derived base-change transformation. -/
noncomputable def rightMate
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a') :
    a' ⋙ pushforwardCohomologyIn g' ⟶ pushforwardCohomologyIn g ⋙ a :=
  conjugateEquiv
    ((pullbackPushforwardAdjunction g').comp f'Adj)
    (fAdj.comp (pullbackPushforwardAdjunction g))
    (map g' f' f g sq)

/-- Taking the inverse mate of the right-adjoint base-change transformation recovers the
canonical derived base-change transformation. -/
theorem rightMate_mate
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a') :
    (conjugateEquiv
      ((pullbackPushforwardAdjunction g').comp f'Adj)
      (fAdj.comp (pullbackPushforwardAdjunction g))).symm
        (rightMate g' f' f g sq a a' fAdj f'Adj) =
      map g' f' f g sq := sorry

/-- Invertibility of derived base change transfers canonically to its right-adjoint mate. -/
noncomputable instance rightMateIsIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    [IsIso (map g' f' f g sq)] :
    IsIso (rightMate g' f' f g sq a a' fAdj f'Adj) := sorry

/-- For a cartesian square of quasi-compact quasi-separated schemes, Tor independence
makes the right-adjoint base-change mate invertible. -/
theorem rightMate_isIso_of_torIndependent
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj) := sorry

/-- For a cartesian square of quasi-compact quasi-separated schemes, flatness of the
horizontal base-change morphism makes the right-adjoint base-change mate invertible. -/
theorem rightMate_isIso_of_flat
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat g]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a') :
    IsIso (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange
