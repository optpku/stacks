module

public import Mathlib.Topology.Sheaves.Sheafify
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open TopCat

universe u

section

/- The bundled owner `TopCat.Presheaf.sheafify` already contains the source assertion as its
`property` field, so the source-facing surface is a tagged check rather than a duplicate theorem. -/

recall TopCat.Presheaf.sheafify

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

/- Lemma 6.17.1: for a set-valued presheaf `ℱ` on `X`, the associated presheaf `ℱ^#`,
formalized by the underlying presheaf of `ℱ.sheafify`, is a sheaf. This is the sheaf-condition
proof carried by the canonical owner `TopCat.Presheaf.sheafify`. -/
@[stacks 007Y "the associated presheaf is a sheaf"]
#check (ℱ.sheafify.property : ℱ.sheafify.presheaf.IsSheaf)

end
