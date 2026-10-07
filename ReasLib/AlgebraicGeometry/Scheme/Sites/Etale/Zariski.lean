module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Every Zariski covering family of schemes is an étale covering family. -/
theorem zariskiPrecoverage_le_etalePrecoverage :
    zariskiPrecoverage ≤ etalePrecoverage := sorry

/-- The standard étale topology is not the Zariski topology. -/
theorem etale_ne_zariski : StandardTopology.etale ≠ StandardTopology.zariski := sorry

end AlgebraicGeometry.Scheme
