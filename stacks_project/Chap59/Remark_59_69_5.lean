/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup
open AlgebraicGeometry.RootsOfUnity AlgebraicGeometry.GroupScheme AlgebraicGeometry.Scheme

universe u

/- Remark 59.69.5 (1): The multiplicative group is the punctured affine line. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.multiplicativeGroup_eq_puncturedAffineLine :
    ∀ (k : Type u) [Field k], Gm k ≅ puncturedAffineLine k)

/- Remark 59.69.5 (2): The multiplicative group is the projective line minus zero and infinity. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.multiplicativeGroup_eq_puncturedProjectiveLine :
    ∀ (k : Type u) [Field k], Gm k ≅ puncturedProjectiveLine k)

/- Remark 59.69.5 (3): Kummer cohomology is canonically the cyclic group. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.etaleCohomology_Gm_rootsOfUnity_h1 :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] [IsAlgClosed k] (h_pos : 0 < n) (h_n : IsUnit (n : k)), h1Roots k n ≃+ ZMod n)

/- Remark 59.69.5 (4): The field power cover defines the canonical Kummer class. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.canonicalClass :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] (h_pos : 0 < n) (h_n : IsUnit (n : k)), h1Roots k n)

/- Remark 59.69.5 (5): The canonical comparison sends the Kummer class to one. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.etaleCohomology_Gm_rootsOfUnity_h1_canonicalClass :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] [IsAlgClosed k] (h_pos : 0 < n) (h_n : IsUnit (n : k)),
      etaleCohomology_Gm_rootsOfUnity_h1 n h_pos h_n (canonicalClass n h_pos h_n) =
        (1 : ZMod n))

/- Remark 59.69.5 (6): Field-map pullback preserves the canonical Kummer class. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.canonicalClass_pullback :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] {k' : Type u} [Field k'] [Algebra k k']
      [HasSheafify (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1})]
      [((smallEtalePullback (gmMap k k')).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Gm k).smallEtaleTopology (Gm k').smallEtaleTopology).IsRightAdjoint] (h_pos : 0 < n) (h_n : IsUnit (n : k)) (h_n' : IsUnit (n : k')),
      rootsH1Pullback (gmMap k k') n (canonicalClass (k := k) n h_pos h_n) =
        canonicalClass (k := k') n h_pos h_n')

/- Remark 59.69.5 (7): The integral power cover is a roots-of-unity fppf torsor. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.powerMap_isTorsor :
    ∀ (n : ℕ) [NeZero n], IsTorsorFor (μₙ n over GmInt.{u}).toGrp (powerMapTorsor n)
      StandardTopology.fppf.precoverage)

/- Remark 59.69.5 (8): Constant-coefficient cohomology is canonically the character group. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.etaleCohomology_Gm_constantZMod_h1 :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] [IsAlgClosed k] (h_pos : 0 < n) (h_n : IsUnit (n : k)),
      h1Constant k n ≃+ (Additive (rootsOfUnity n k) →+ ZMod n))

/- Remark 59.69.5 (9): The character comparison commutes with maps of algebraically closed fields. -/
@[stacks 0A44] #check
  (AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup.etaleCohomology_Gm_constantZMod_h1_naturality :
    ∀ (n : ℕ) {k : Type u} [Field k]
      [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] [IsAlgClosed k] {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
      [HasSheafify (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1}]
      [HasExt.{u + 1} (Sheaf (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1})]
      [((smallEtalePullback (gmMap k k')).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Gm k).smallEtaleTopology (Gm k').smallEtaleTopology).IsRightAdjoint] (h_pos : 0 < n) (h_n : IsUnit (n : k)) (h_n' : IsUnit (n : k'))
      (x : h1Constant k n),
      (etaleCohomology_Gm_constantZMod_h1 (k := k') n h_pos h_n'
        (constantH1Pullback (gmMap k k') n x)).comp
          (restrictRootsOfUnity (algebraMap k k') n).toAdditive =
        etaleCohomology_Gm_constantZMod_h1 (k := k) n h_pos h_n x)

end
