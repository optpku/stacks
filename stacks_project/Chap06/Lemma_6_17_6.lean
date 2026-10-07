module

public import ReasLib.Topology.Sheaves.Types.Sheafification
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable {F G : X.Presheaf (Type u)} (φ : F ⟶ G)

/- The categorical owners are `Mono` and `Epi`; the preservation statements below use their
sectionwise views as explicit hypotheses, while the output uses mathlib's local-surjectivity
predicate where that is the actual sheaf-theoretic notion. -/

/- Lemma 6.17.6 (1): sheafification sends a surjective morphism of presheaves of sets on `X` to
a surjective morphism of sheaves. -/
@[stacks 0H7I "sheafification preserves surjective morphisms of presheaves of sets"]
#check TopCat.Presheaf.isLocallySurjective_presheafToSheaf_map_of_app_surjective φ

/- Lemma 6.17.6 (2): sheafification sends an injective morphism of presheaves of sets on `X` to
an injective morphism of sheaves. -/
@[stacks 0H7I "sheafification preserves injective morphisms of presheaves of sets"]
#check TopCat.Presheaf.app_injective_presheafToSheaf_map_of_app_injective φ

end
