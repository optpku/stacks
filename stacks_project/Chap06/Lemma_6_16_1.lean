module

public import ReasLib.Topology.Sheaves.Types.Morphisms
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopCat.Presheaf

universe u

variable {X : TopCat.{u}} {ℱ 𝒢 : X.Sheaf (Type u)} (φ : ℱ ⟶ 𝒢)

/- Lemma 6.16.1 (1): a morphism of sheaves of sets on `X` is a monomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is injective. -/
@[stacks 007T "monomorphisms are detected by injectivity on stalks"]
#check TopCat.Sheaf.mono_iff_stalk_injective φ

/- Lemma 6.16.1 (2): a morphism of sheaves of sets on `X` is an epimorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is surjective. -/
@[stacks 007T "epimorphisms are detected by surjectivity on stalks"]
#check TopCat.Sheaf.epi_iff_stalk_surjective φ

/- Lemma 6.16.1 (3): a morphism of sheaves of sets on `X` is an isomorphism if and only if each
stalk map `φ_x : ℱ_x → 𝒢_x` is bijective. -/
@[stacks 007T "isomorphisms are detected by bijectivity on stalks"]
#check TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ

/- For maps in `Type`, the stalkwise isomorphism condition is exactly bijectivity. -/
#check CategoryTheory.bijective_iff_isIso_ofHom
