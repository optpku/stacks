module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage

/-!
# Source-locality of étale-local lifts

If a scheme-morphism property is étale local on the source-and-target and τ-local
on the source, then its lift to morphisms of algebraic spaces is τ-local on the
source, for τ among fpqc, fppf, syntomic, smooth, and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a scheme-morphism property `P` is étale local on the source-and-target and
fpqc local on the source, then `etaleLocal P` is fpqc local on the source. -/
instance etaleLocal_isLocalAtSource_fpqc {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsLocalAtSource Scheme.fpqcPrecoverage] :
    (etaleLocal P).IsLocalAtSource (fpqcPrecoverage S) :=
  sorry

/-- If a scheme-morphism property `P` is étale local on the source-and-target and
fppf local on the source, then `etaleLocal P` is fppf local on the source. -/
instance etaleLocal_isLocalAtSource_fppf {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsLocalAtSource Scheme.fppfPrecoverage] :
    (etaleLocal P).IsLocalAtSource (fppfPrecoverage S) :=
  sorry

/-- If a scheme-morphism property `P` is étale local on the source-and-target and
syntomic local on the source, then `etaleLocal P` is syntomic local on the
source. -/
instance etaleLocal_isLocalAtSource_syntomic {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage] :
    (etaleLocal P).IsLocalAtSource (precoverage (@Syntomic S)) :=
  sorry

/-- If a scheme-morphism property `P` is étale local on the source-and-target and
smooth local on the source, then `etaleLocal P` is smooth local on the source. -/
instance etaleLocal_isLocalAtSource_smooth {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsLocalAtSource Scheme.bigSmoothPrecoverage] :
    (etaleLocal P).IsLocalAtSource (precoverage (@Smooth S)) :=
  sorry

/-- If a scheme-morphism property `P` is étale local on the source-and-target and
étale local on the source, then `etaleLocal P` is étale local on the source. -/
instance etaleLocal_isLocalAtSource_etale {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsLocalAtSource Scheme.etalePrecoverage] :
    (etaleLocal P).IsLocalAtSource (@etalePrecoverage S) :=
  sorry

/-- A morphism of algebraic spaces has the lift of `P` if and only if it has the
lift after precomposition with every member of an fpqc covering of the source. -/
theorem etaleLocal_fpqc_iff_forall_comp {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [(etaleLocal P).IsLocalAtSource (fpqcPrecoverage S)]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (fpqcPrecoverage S).ZeroHypercover X) :
    etaleLocal P f ↔ ∀ i, etaleLocal P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism of algebraic spaces has the lift of `P` if and only if it has the
lift after precomposition with every member of an fppf covering of the source. -/
theorem etaleLocal_fppf_iff_forall_comp {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [(etaleLocal P).IsLocalAtSource (fppfPrecoverage S)]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (fppfPrecoverage S).ZeroHypercover X) :
    etaleLocal P f ↔ ∀ i, etaleLocal P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism of algebraic spaces has the lift of `P` if and only if it has the
lift after precomposition with every member of a syntomic covering of the
source. -/
theorem etaleLocal_syntomic_iff_forall_comp {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [(etaleLocal P).IsLocalAtSource (precoverage (@Syntomic S))]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (precoverage (@Syntomic S)).ZeroHypercover X) :
    etaleLocal P f ↔ ∀ i, etaleLocal P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism of algebraic spaces has the lift of `P` if and only if it has the
lift after precomposition with every member of a smooth covering of the
source. -/
theorem etaleLocal_smooth_iff_forall_comp {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [(etaleLocal P).IsLocalAtSource (precoverage (@Smooth S))]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (precoverage (@Smooth S)).ZeroHypercover X) :
    etaleLocal P f ↔ ∀ i, etaleLocal P (𝒰.f i ≫ f) :=
  sorry

/-- A morphism of algebraic spaces has the lift of `P` if and only if it has the
lift after precomposition with every member of an étale covering of the
source. -/
theorem etaleLocal_etale_iff_forall_comp {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [(etaleLocal P).IsLocalAtSource (@etalePrecoverage S)]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : (@etalePrecoverage S).ZeroHypercover X) :
    etaleLocal P f ↔ ∀ i, etaleLocal P (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
