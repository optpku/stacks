/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Residue algebra of an object of `C_Λ`

An object `A` of `ArtinianLocalAlgCat Λ k` carries a canonical `Λ`-algebra surjection
`A.carrier → k`, obtained by composing `IsLocalRing.residue` with the chosen residue-field
identification. This makes the extended conormal sequence available on objects of `C_Λ`.
-/

@[expose] public section

open IsLocalRing

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- The scalar action, tower and residue-map facts have a single ReasLib owner. -/
#check (residueAlgebra : ∀ (A : ArtinianLocalAlgCat Λ k), Algebra A.carrier k)

#check (instIsScalarTowerResidue :
  ∀ (A : ArtinianLocalAlgCat Λ k), IsScalarTower Λ A.carrier k)

#check (residueAlgebra_algebraMap :
  ∀ (A : ArtinianLocalAlgCat Λ k), algebraMap A.carrier k = (toResidueHom A).toRingHom)

#check (toResidueHom_surjective :
  ∀ (A : ArtinianLocalAlgCat Λ k), Function.Surjective (toResidueHom A))

#check (ker_toResidueHom :
  ∀ (A : ArtinianLocalAlgCat Λ k),
    RingHom.ker (toResidueHom A).toRingHom = maximalIdeal A.carrier)

end ArtinianLocalAlgCat
