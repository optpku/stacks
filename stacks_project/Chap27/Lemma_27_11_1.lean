/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Twist

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

/-!
Source bridge for the natural domain of a graded `Proj` map, its comparison of explicit coherent
twist graded algebras, and the properties that characterize the resulting map.
-/

universe u

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]
  (PcalA : AlgebraicGeometry.ProjTwistPresentation calA)
  (PcalB : AlgebraicGeometry.ProjTwistPresentation calB)
  (psi : calA →+*ᵍ calB)
  (hProj : AlgebraicGeometry.ProjMap PcalA PcalB psi)

/- Lemma 27.11.1: a graded ring map has a canonical map on its natural projective-spectrum
domain together with the canonical comparison of all integral twists, where the explicit
presentations model the actual coherent twist graded algebras. -/
@[stacks 01MY] #check
  (AlgebraicGeometry.projMap PcalA PcalB psi :
    AlgebraicGeometry.ProjMap PcalA PcalB psi)

#check
  (AlgebraicGeometry.ProjMap.theta_compatibility_spec
      (AlgebraicGeometry.projMap PcalA PcalB psi) :
    AlgebraicGeometry.ProjMap.projMapThetaCompatibility PcalA PcalB psi
      (AlgebraicGeometry.projMap PcalA PcalB psi).map
      (AlgebraicGeometry.projMap PcalA PcalB psi).theta)

#check
  (AlgebraicGeometry.ProjMap.basicOpen_spec
      (AlgebraicGeometry.projMap PcalA PcalB psi) :
    AlgebraicGeometry.ProjMap.projMapBasicOpenCompatibility psi
      (AlgebraicGeometry.projMap PcalA PcalB psi).map)

#check
  (AlgebraicGeometry.ProjMap.eq_projMap hProj :
    hProj = AlgebraicGeometry.projMap PcalA PcalB psi)

end
