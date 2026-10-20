/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PushforwardAlgebra
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Quasi-coherent pushforward structure algebras

The direct image of the structure sheaf along a quasi-compact quasi-separated morphism
is a quasi-coherent algebra over the structure sheaf of the target.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The quasi-coherent `𝒪_Y`-algebra `f_* 𝒪_X` attached to a qcqs morphism. -/
def pushforwardStructureQcAlgebra {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] : Y.QcAlgebraUnder where
  obj := Under.mk (commStructureSheafMap f)
  property := sorry

/-- Forgetting commutativity in `pushforwardStructureQcAlgebra f` recovers the ring-valued
pushforward of `𝒪_X`. -/
theorem pushforwardStructureQcAlgebra_forget₂ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (pushforwardStructureQcAlgebra f).obj.right =
      pushforwardStructureAlgebra f :=
  sorry

/-- The sheaf of `pushforwardStructureQcAlgebra f` is the commutative-ring pushforward of
`𝒪_X`. -/
theorem pushforwardStructureQcAlgebra_sheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    (pushforwardStructureQcAlgebra f).obj.right =
      (commRingPushforward f).obj (commStructureSheaf X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
