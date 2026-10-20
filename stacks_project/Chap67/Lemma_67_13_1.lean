/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
import StacksCheckRecall

/-! # Closed subspaces and quasi-coherent ideals

All clauses of Stacks 03MB reuse the public ideal owner. Closed subspaces
are compared up to isomorphism over their ambient space; inclusions reverse
the ideal order, and factorization is equivalent to ideal vanishing.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.13.1. Closed immersions have quasi-coherent pushforward structure
modules and kernel ideals; these ideals classify closed subspaces with reversed
inclusion and characterize factorization by vanishing. -/
@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.pushforwardUnit_isQuasicoherent :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
      ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))).IsQuasicoherent)

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafMap_epi :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
      Epi (Hom.idealSheafMap i))

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsQuasiCoherent_idealSheafSubobject :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
      IsQuasiCoherent (Hom.idealSheafSubobject i))

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X) [IsQuasiCoherent I],
      (ClosedSubspace.ofQuasiCoherentIdeal I).idealSheaf = I)

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.overIso_iff_idealSheaf_eq :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z W : ClosedSubspace X),
      Nonempty (Over.mk Z.ι ≅ Over.mk W.ι) ↔ Z.idealSheaf = W.idealSheaf)

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.idealSheaf_le_iff :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z W : ClosedSubspace X),
      W.idealSheaf ≤ Z.idealSheaf ↔ ∃ f : Z.X ⟶ W.X, f ≫ W.ι = Z.ι)

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.exists_lift_iff_vanishes :
    ∀ {S : Scheme.{u}} {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      (h : Y ⟶ X),
      (∃ φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i))

@[stacks 03MB] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.existsUnique_lift_iff_vanishes :
    ∀ {S : Scheme.{u}} {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      (h : Y ⟶ X),
      (∃! φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i))
