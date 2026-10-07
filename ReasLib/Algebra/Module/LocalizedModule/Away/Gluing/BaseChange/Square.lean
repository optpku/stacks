module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange.Composition
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.OfModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of principal-open gluing over a commutative square

The two iterated base changes attached to a commutative square of ring maps
are compared through the composition isomorphism for gluing base change.

@stack 05EQ
-/

@[expose] public section

open CategoryTheory

universe u w

noncomputable section

namespace LocalizedModule.Away.Gluing

variable {R S Rp Sp : Type u}
variable [CommRing R] [CommRing S] [CommRing Rp] [CommRing Sp]
variable {ι : Type w} {f : ι → R}

/-- Transport principal-open gluing data along an equality of the indexing
family.  The equality changes only the family index; no local module or
overlap map is chosen. -/
@[stacks 05EQ "principal-open gluing family transport"]
noncomputable def changeFamilyFunctor {A : Type u} [CommRing A]
    {g h : ι → A} (e : g = h) : Gluing g ⥤ Gluing h :=
  match e with
  | rfl => 𝟭 _

/-- Transporting the gluing attached to a global module along an equality of
families recovers the gluing attached to the target family. -/
@[stacks 05EQ "principal-open global-module gluing family transport"]
noncomputable def changeFamilyOfModuleIso {A : Type u} [CommRing A]
    {g h : ι → A} (e : g = h) (M : ModuleCat A) :
    (changeFamilyFunctor e).obj (ofModule g M) ≅ ofModule h M :=
  match e with
  | rfl => Iso.refl _

/-- Transport along an equality of families after transport along its
inverse canonically cancels. -/
@[stacks 05EQ "principal-open gluing inverse family transport"]
noncomputable def changeFamilyInvIso {A : Type u} [CommRing A]
    {g h : ι → A} (e : g = h) (X : Gluing h) :
    (changeFamilyFunctor e).obj ((changeFamilyFunctor e.symm).obj X) ≅ X :=
  match h, e, X with
  | _, rfl, X => Iso.refl X

/-- Equal ring maps induce naturally isomorphic gluing base-change functors,
after making the induced family transport explicit. -/
@[stacks 05EQ "principal-open gluing base change under equal ring maps"]
noncomputable def baseChangeCongrNatIso {κ κ' : R →+* Sp} (h : κ = κ') :
    baseChangeFunctor (f := f) κ ≅
      baseChangeFunctor κ' ⋙
        changeFamilyFunctor
          (congrArg (fun k : R →+* Sp ↦ fun i ↦ k (f i)) h).symm :=
  match h with
  | rfl => (Functor.rightUnitor _).symm

/-- The natural comparison between the two iterated gluing base-change
functors attached to a commutative square of ring maps. -/
@[stacks 05EQ "principal-open gluing commutative-square base-change natural isomorphism"]
noncomputable def baseChangeCommSqNatIso
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) :
    baseChangeFunctor (f := f) φ ⋙ baseChangeFunctor θ ≅
      baseChangeFunctor ψ ⋙ baseChangeFunctor φp ⋙
        changeFamilyFunctor
          (congrArg (fun k : R →+* Sp ↦ fun i ↦ k (f i)) hcomm).symm :=
  baseChangeCompNatIso φ θ ≪≫
    baseChangeCongrNatIso hcomm ≪≫
      Functor.isoWhiskerRight (baseChangeCompNatIso ψ φp).symm
        (changeFamilyFunctor
          (congrArg (fun k : R →+* Sp ↦ fun i ↦ k (f i)) hcomm).symm)

/-- The objectwise comparison between the two iterated gluing base changes
attached to a commutative square of ring maps.  The second object is visibly
transported along the induced equality of principal-open families. -/
@[stacks 05EQ "principal-open gluing commutative-square base-change comparison"]
noncomputable def baseChangeCommSqIso (X : Gluing f)
    (φ : R →+* S) (ψ : R →+* Rp) (θ : S →+* Sp) (φp : Rp →+* Sp)
    (hcomm : θ.comp φ = φp.comp ψ) :
    (X.baseChange φ).baseChange θ ≅
      (changeFamilyFunctor
        (congrArg (fun k : R →+* Sp ↦ fun i ↦ k (f i)) hcomm).symm).obj
          ((X.baseChange ψ).baseChange φp) :=
  (baseChangeCommSqNatIso φ ψ θ φp hcomm).app X

end LocalizedModule.Away.Gluing
