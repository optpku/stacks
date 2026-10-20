/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Classical

/-!
# The classical base object of `CompleteLocalAlgCat`

In the classical case, the base is initial among complete local algebras.
The structure morphisms and initiality API are available from their mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ArtinianLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] [IsClassical Λ k]

namespace CompleteLocalAlgCat

#check (CompleteLocalAlgCat.classical : CompleteLocalAlgCat Λ k)
#check (CompleteLocalAlgCat.classical_carrier :
  (classical : CompleteLocalAlgCat Λ k).carrier = Λ)
#check (CompleteLocalAlgCat.instIsLocalHom_algebraMap_classical :
  ∀ R : CompleteLocalAlgCat Λ k, IsLocalHom (algebraMap Λ R.carrier))
#check (CompleteLocalAlgCat.fromClassical_residue_compat :
  ∀ R : CompleteLocalAlgCat Λ k,
    residueCompat (A := classical) (B := R) (Algebra.ofId Λ R.carrier)
      ⟨(instIsLocalHom_algebraMap_classical R).map_nonunit⟩ = residueIsoHom classical)
#check (CompleteLocalAlgCat.fromClassical :
  ∀ R : CompleteLocalAlgCat Λ k, classical ⟶ R)
#check (CompleteLocalAlgCat.fromClassical_hom :
  ∀ R : CompleteLocalAlgCat Λ k, (fromClassical R).hom = Algebra.ofId Λ R.carrier)
#check (CompleteLocalAlgCat.fromClassical_unique :
  ∀ {R : CompleteLocalAlgCat Λ k} (f : classical ⟶ R), f = fromClassical R)
#check (CompleteLocalAlgCat.classicalIsInitial :
  IsInitial (classical : CompleteLocalAlgCat Λ k))
#check (CompleteLocalAlgCat.classicalIsInitial_to :
  ∀ R : CompleteLocalAlgCat Λ k, IsInitial.to classicalIsInitial R = fromClassical R)
#check (CompleteLocalAlgCat.instHasInitial_classical : HasInitial (CompleteLocalAlgCat Λ k))

end CompleteLocalAlgCat
