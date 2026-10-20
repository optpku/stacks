module

public import ReasLib.CategoryTheory.Sites.LocalIsoDescent

/-!
# Descent of a map constant on the fibres of a locally surjective map

Unlike a local isomorphism, a quotient map need not be locally injective. A supplied map
constant on its fibres still descends to a sheaf: send its actual local preimages through
the given map and amalgamate that family. The family is the same native local-preimage
family used by `LocalIsoDescent`; only its compatibility hypothesis changes.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Presheaf.LocalSectionDescent

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {P U F : Cᵒᵖ ⥤ Type w} (η : P ⟶ U) (g : P ⟶ F)
variable [hη : Presheaf.IsLocallySurjective J η]
variable (hF : Presheaf.IsSheaf J F)
variable (hfibre : ∀ (T : Cᵒᵖ) (x y : P.obj T),
  η.app T x = η.app T y → g.app T x = g.app T y)

include hfibre in
/-- The actual local-preimage image family is compatible because its images depend only
on the section downstairs. No local injectivity of the quotient map is required. -/
theorem family_compatible {T : Cᵒᵖ} (x : U.obj T) :
    (LocalIsoDescent.family η g x).Compatible := sorry

/-- Descend a section by gluing the images of its actual local preimages. -/
def app {T : Cᵒᵖ} (x : U.obj T) : F.obj T :=
  ((isSheaf_iff_isSheaf_of_type J F).mp hF _ (Presheaf.imageSieve_mem J η x)).amalgamate
    (LocalIsoDescent.family η g x) (family_compatible η g hfibre x)

/-- Restricting the descended section to a local lift evaluates the given map on that lift. -/
theorem app_restrict {T : Cᵒᵖ} (x : U.obj T) {V : C}
    (f : V ⟶ T.unop) (hf : Presheaf.imageSieve η x f) :
    F.map f.op (app J η g hF hfibre x) =
      g.app (op V) (Presheaf.localPreimage η x f hf) :=
  Presieve.IsSheafFor.valid_glue _ (family_compatible η g hfibre x) f hf

/-- The gluing construction commutes with restrictions by uniqueness of sheaf amalgamation. -/
theorem app_natural {T V : Cᵒᵖ} (f : T ⟶ V) (x : U.obj T) :
    F.map f (app J η g hF hfibre x) =
      app J η g hF hfibre (U.map f x) := sorry

/-- The descended natural transformation has the specified local-gluing component functions. -/
def descend : U ⟶ F where
  app T := TypeCat.ofHom (app J η g hF hfibre)
  naturality T V f := by
    ext x
    exact (app_natural J η g hF hfibre f x).symm

/-- The descended map recovers the original map on the actual covering source. -/
theorem descend_fac : η ≫ descend J η g hF hfibre = g := sorry

/-- Local surjectivity and separation uniquely determine the descended map. -/
theorem descend_unique (k : U ⟶ F) (hk : η ≫ k = g) :
    k = descend J η g hF hfibre := sorry

end CategoryTheory.Presheaf.LocalSectionDescent
