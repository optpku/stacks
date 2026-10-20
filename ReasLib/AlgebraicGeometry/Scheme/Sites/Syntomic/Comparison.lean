module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every smooth covering family of schemes is a syntomic covering family. -/
theorem bigSmoothPrecoverage_le_bigSyntomicPrecoverage :
    bigSmoothPrecoverage.{u} ≤ bigSyntomicPrecoverage.{u} := sorry

/-- Every étale covering family of schemes is a syntomic covering family. -/
theorem etalePrecoverage_le_bigSyntomicPrecoverage :
    etalePrecoverage.{u} ≤ bigSyntomicPrecoverage.{u} := sorry

/-- Every Zariski covering family of schemes is a syntomic covering family. -/
theorem zariskiPrecoverage_le_bigSyntomicPrecoverage :
    zariskiPrecoverage.{u} ≤ bigSyntomicPrecoverage.{u} := sorry

end AlgebraicGeometry.Scheme
