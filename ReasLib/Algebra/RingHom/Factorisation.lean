/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Factorisation
public import ReasLib.Algebra.RingHom.ULift

@[expose] public section

/-!
# Factorisations of ring homomorphisms

This is the map-facing, cross-universe view of mathlib's categorical
`CategoryTheory.Factorisation`.
-/

open CategoryTheory

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A categorical factorisation of a ring homomorphism, with only its
source and target lifted to a common universe. -/
@[stacks 0BJ7 "ring-homomorphism factorisation"]
abbrev Factorisation (f : R →+* S) :=
  CategoryTheory.Factorisation (CommRingCat.ofHom f.ulift.{v, u})

namespace Factorisation

variable {f : R →+* S}

/-- The lifted categorical triangle used by `Factorisation.ofMaps`. -/
@[stacks 0BJ7 "lifted triangle for a factorisation from ring maps"]
theorem ofMaps_comp {T : Type (max u v)} [CommRing T]
    (fromSource : R →+* T) (toTarget : T →+* S)
    (factor : toTarget.comp fromSource = f) :
    CommRingCat.ofHom (fromSource.comp ULift.ringEquiv.toRingHom) ≫
        CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp toTarget) =
      CommRingCat.ofHom (f.ulift.{v, u}) := sorry

/-- Build a bundled ring-homomorphism factorisation from its midpoint, two
maps, and their factorisation equation. -/
@[stacks 0BJ7 "factorisation from ring maps"]
noncomputable def ofMaps {T : Type (max u v)} [CommRing T]
    (fromSource : R →+* T) (toTarget : T →+* S)
    (factor : toTarget.comp fromSource = f) : f.Factorisation where
  mid := CommRingCat.of T
  ι := CommRingCat.ofHom (fromSource.comp ULift.ringEquiv.toRingHom)
  π := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp toTarget)
  ι_π := ofMaps_comp fromSource toTarget factor

/-- The map from the source to the midpoint of a ring-homomorphism
factorisation. -/
@[stacks 0BJ7 "factorisation map from the unlifted source"]
noncomputable def fromSource (F : f.Factorisation) : R →+* F.mid :=
  F.ι.hom.comp
    (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom

/-- The map from the midpoint to the original, unlifted target. -/
@[stacks 0BJ7 "factorisation map to the unlifted target"]
noncomputable def toTarget (F : f.Factorisation) : F.mid →+* S :=
  (ULift.ringEquiv : ULift.{u} S ≃+* S).toRingHom.comp F.π.hom

/-- The two map-facing projections of a ring-homomorphism factorisation
compose to the original map. -/
@[stacks 0BJ7 "ring-homomorphism factorisation equation"]
theorem factor (F : f.Factorisation) :
    F.toTarget.comp F.fromSource = f := sorry

/-- The source map of a factorisation built by `ofMaps`. -/
@[stacks 0BJ7 "source map of a factorisation from ring maps", simp]
theorem fromSource_ofMaps {T : Type (max u v)} [CommRing T]
    (fromSource : R →+* T) (toTarget : T →+* S)
    (factor : toTarget.comp fromSource = f) :
    (ofMaps fromSource toTarget factor).fromSource = fromSource := sorry

/-- The target map of a factorisation built by `ofMaps`. -/
@[stacks 0BJ7 "target map of a factorisation from ring maps", simp]
theorem toTarget_ofMaps {T : Type (max u v)} [CommRing T]
    (fromSource : R →+* T) (toTarget : T →+* S)
    (factor : toTarget.comp fromSource = f) :
    (ofMaps fromSource toTarget factor).toTarget = toTarget := sorry

end Factorisation

end RingHom
