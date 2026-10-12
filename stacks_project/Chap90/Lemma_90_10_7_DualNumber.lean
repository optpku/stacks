/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-! Lemma 90.10.7: residue morphism compatibility checks. -/
#check (toResidue : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  A ⟶ residue Λ k)

#check (toResidue_hom : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  (toResidue A).hom = toResidueHom A)

#check (toResidue_spec : ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k] (A : ArtinianLocalAlgCat Λ k),
  IsLocalHom (toResidue A).hom ∧
    residueCompat (toResidue A).hom (toResidue A).isLocalHom = residueIsoHom A)

end ArtinianLocalAlgCat
