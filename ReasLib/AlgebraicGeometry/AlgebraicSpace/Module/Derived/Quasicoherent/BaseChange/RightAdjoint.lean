/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-! # Right-adjoint derived base change

The canonical derived base-change transformation induces a right-adjoint mate,
which is invertible for Tor-independent cartesian squares.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

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
    ((pullbackPushforwardCohomologyAdjunction g').comp f'Adj)
    (fAdj.comp (pullbackPushforwardCohomologyAdjunction g))
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
      ((pullbackPushforwardCohomologyAdjunction g').comp f'Adj)
      (fAdj.comp (pullbackPushforwardCohomologyAdjunction g))).symm
        (rightMate g' f' f g sq a a' fAdj f'Adj) =
      map g' f' f g sq :=
  sorry

/-- Invertibility of derived base change transfers canonically to its right-adjoint mate. -/
noncomputable instance rightMateIsIso
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : CommSq g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    [IsIso (map g' f' f g sq)] :
    IsIso (rightMate g' f' f g sq a a' fAdj f'Adj) :=
  sorry

/-- For a cartesian square of algebraic spaces, Tor independence makes the
right-adjoint base-change mate invertible. -/
theorem rightMate_isIso_of_torIndependent
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsIso (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj) :=
  sorry

section Square

variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
variable [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
variable (sq : IsPullback g' f' f g)
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
variable (fAdj : pushforwardCohomologyIn f ⊣ a)
variable (f'Adj : pushforwardCohomologyIn f' ⊣ a')
variable (hTor : TorIndependentOver (Over.mk f) (Over.mk g))

/-- The twisted base-change transformation is the mate of the inverse of the
right-adjoint mate of ordinary derived base change. -/
def twistedMap : a ⋙ pullback g' ⟶ pullback g ⋙ a' :=
  CategoryTheory.DerivedBaseChange.mapOfRight
    (pullbackPushforwardCohomologyAdjunction g)
    (pullbackPushforwardCohomologyAdjunction g')
    (@asIso _ _ _ _ (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
      (rightMate_isIso_of_torIndependent g' f' f g sq a a' fAdj f'Adj hTor)).inv

/-- The defining mate equation identifies the twisted map with the inverse of the
canonical right-adjoint base-change mate. -/
theorem twistedMap_mate :
    (mateEquiv (pullbackPushforwardCohomologyAdjunction g)
      (pullbackPushforwardCohomologyAdjunction g'))
        (twistedMap g' f' f g sq a a' fAdj f'Adj hTor) =
      (@asIso _ _ _ _ (rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
        (rightMate_isIso_of_torIndependent g' f' f g sq a a' fAdj f'Adj hTor)).inv := sorry

end Square

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
