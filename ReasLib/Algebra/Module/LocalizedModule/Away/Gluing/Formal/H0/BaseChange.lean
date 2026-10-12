/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal.H0.Adjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero formal-gluing base change

The right mate of the canonical `Can` base-change isomorphism is the
base-change map on degree-zero formal-gluing sections.  Invertibility is a
separate property of the ring square and is not built into this general map.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory

universe u w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S Rp Sp : Type u}
variable [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sp]
variable {ι : Type w} {f : ι → R}

/-- The canonical degree-zero base-change transformation attached to a
commutative square of ring maps.  It is the right mate of
`canBaseChangeNatIso`. -/
@[stacks 05EQ "formal gluing degree-zero base-change transformation"]
noncomputable def h0BaseChangeNatTrans
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) :
    h0Functor (φ := φ) (f := f) ⋙ ModuleCat.extendScalars ψ ⟶
      baseChangeFunctor φ ψ θ φp hcomm ⋙
        h0Functor (φ := φp) (f := fun i ↦ ψ (f i)) :=
  CategoryTheory.DerivedBaseChange.map
    (h0Adjunction (φ := φ) (f := f))
    (h0Adjunction (φ := φp) (f := fun i ↦ ψ (f i)))
    (canBaseChangeNatIso (f := f) φ ψ θ φp hcomm)

/-- The component of the canonical degree-zero base-change transformation at
a formal gluing object. -/
@[stacks 05EQ "formal gluing degree-zero base-change component"]
noncomputable abbrev h0BaseChangeApp
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ)
    (X : FormalGluing.{u, w, w} φ f) :
    (ModuleCat.extendScalars ψ).obj (h0Functor.obj X) ⟶
      h0Functor.obj ((baseChangeFunctor φ ψ θ φp hcomm).obj X) :=
  (h0BaseChangeNatTrans φ ψ θ φp hcomm).app X

end LocalizedModule.Away.FormalGluing
