module

public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Sections
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicTopology Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

universe u

/- Remark 96.19.4: for a 1-morphism `f : U ⟶ X` of categories fibred in groupoids
over `(Sch/S)_fppf`, an abelian presheaf `F` on `X`, and an object `x` of `X`
lying over a scheme `W` (so `p(x) = W`), the value `Γ(x, RelativeCech.complex f F)`
of the relative Čech complex equals the ordinary Čech complex of the base change
`g : V ⟶ Y` of `f` to `X / x ≅ Y`, where `Y = GroupoidsOver.slice W` and
`V = yonedaFibreProduct f x`. Explicitly
`(RelativeCech.complex f F).asFunctor.obj (op x.1) ≅
Cech.complex (RelativeCech.yonedaBaseChange f x)
(Cech.inverseImage (YonedaSlice.representative x) F)`.
The covering simplex map `V_n ⟶ U_n` of Lemma 96.18.1 induces an equivalence
`V_n ≃ (Sch/W)_fppf ×_{x, X} U_n`, so 96.5.0.1 supplies the degreewise
identification. In particular, results on the ordinary Čech complex such as
Lemma 96.18.2 imply results for the relative Čech complex such as Lemma 96.19.3. -/
@[stacks 06XB] #check
  (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.sectionsHom.isIso :
    ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) {W : Over S}
      (x : X.p.Fiber W) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
      IsIso (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.sectionsHom f x F))

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.sectionsHom :
  ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) {W : Over S}
    (x : X.p.Fiber W) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    (RelativeCech.complex f F).asFunctor.obj (op x.1) ⟶
      Cech.complex (RelativeCech.yonedaBaseChange f x)
        (Cech.inverseImage (YonedaSlice.representative x) F))

#check (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.sectionsHom_f.isIso :
  ∀ {S : Scheme.{u}} {U X : GroupoidsOver S} (f : U ⟶ X) {W : Over S}
    (x : X.p.Fiber W) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ),
    IsIso (CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech.sectionsHom_f f x F n))
