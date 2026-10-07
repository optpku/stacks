module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a quasi-coherent module `F` on a scheme `S`, the presheaf of sections
of pullbacks of `F` over schemes over `S` is an fpqc sheaf. -/
theorem pullbackSectionsPresheaf_isSheaf_fpqc
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F).presheaf := sorry

end AlgebraicGeometry.Scheme.Modules
