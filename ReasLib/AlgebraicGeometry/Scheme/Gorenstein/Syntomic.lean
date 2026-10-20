module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic
public import ReasLib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Gorenstein

/-- Gorensteinness is local for the syntomic precoverage of schemes. -/
instance isLocalSyntomic :
    ObjectProperty.IsLocal (Scheme.Gorenstein : ObjectProperty Scheme.{u})
      Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.Scheme.Gorenstein
