module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic

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

end AlgebraicGeometry.AlgebraicSpace
