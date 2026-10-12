/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.StrictHenselian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {R : Type u} [CommRing R]

/-- The small-étale object associated to the basic open `D(a)` of `Spec R`. -/
abbrev specEtaleBasicOpenSection (a : Γ(Spec (.of R), ⊤)) : (Spec (.of R)).Etale :=
  Etale.mk ((Spec (.of R)).basicOpen a).ι

/-- The small-étale object associated to the basic open `D(f)` of `Spec R`. -/
abbrev specEtaleBasicOpen (f : R) : (Spec (.of R)).Etale :=
  specEtaleBasicOpenSection ((ΓSpecIso (.of R)).inv f)

/-- The small-étale morphism restricting sections from `D(f * g)` to `D(g)`. -/
def specEtaleBasicOpenSection_mul_hom (f g : Γ(Spec (.of R), ⊤)) :
    specEtaleBasicOpenSection (f * g) ⟶ specEtaleBasicOpenSection g :=
  MorphismProperty.Over.homMk
    ((Spec (.of R)).homOfLE
      ((basicOpen_mul (Spec (.of R)) f g).trans_le inf_le_right))
    ((Spec (.of R)).homOfLE_ι
      ((basicOpen_mul (Spec (.of R)) f g).trans_le inf_le_right))

/-- The degree-one restriction map from `D(f + g)` to the two multiplied basic opens. -/
def etaleH1RestrictBiproduct
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})
    [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (f g : R) :
    F.H' 1 (specEtaleBasicOpen (f + g)) ⟶
      F.H' 1 (specEtaleBasicOpenSection
          ((ΓSpecIso (.of R)).inv f * (ΓSpecIso (.of R)).inv (f + g))) ⊞
        F.H' 1 (specEtaleBasicOpenSection
          ((ΓSpecIso (.of R)).inv g * (ΓSpecIso (.of R)).inv (f + g))) :=
  biprod.lift
    ((F.cohomologyPresheaf 1).map
      (specEtaleBasicOpenSection_mul_hom
        ((ΓSpecIso (.of R)).inv f) ((ΓSpecIso (.of R)).inv (f + g))).op)
    ((F.cohomologyPresheaf 1).map
      (specEtaleBasicOpenSection_mul_hom
        ((ΓSpecIso (.of R)).inv g) ((ΓSpecIso (.of R)).inv (f + g))).op)

/-- Vanishing of the kernel of the degree-one restriction map on every pair of basic opens. -/
def etaleH1Kernel_basicOpen_add
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})
    [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})] :
    Prop :=
  ∀ f g : R, IsZero (kernel (etaleH1RestrictBiproduct F f g))

/-- If every local ring of `R` is strictly henselian and the basic-open degree-one
kernel vanishes for every pair of elements, then all positive-degree étale
cohomology of the sheaf vanishes. -/
theorem etaleCohomology_isZero_of_h1Kernel_on_basicOpens
    [HasStrictlyHenselianStalks (Spec (.of R))]
    (F : Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})
    [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (h_kernel : etaleH1Kernel_basicOpen_add F) :
    ∀ q : ℕ, 0 < q → IsZero ((Sheaf.functorH (Spec (.of R)).smallEtaleTopology q).obj F) :=
  sorry

end AlgebraicGeometry.Scheme
