/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Functor
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Remark_96_19_4_Comparison

/-!
# The relative Čech complex evaluated on a fibre object

The value of `K^•(f, F)` at a fibre object `x` of `X` is the ordinary Čech
complex of the base change of `f` to `X / x ≅ (Sch/W)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicTopology Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- Remark 96.19.4: for a 1-morphism `f : U ⟶ X` of categories fibred in groupoids
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
@[stacks 06XB]
def relativeCechSectionsIso (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (RelativeCech.complex f F).asFunctor.obj (op x.1) ≅
      Cech.complex (RelativeCech.yonedaBaseChange f x)
        (Cech.inverseImage (YonedaSlice.representative x) F) :=
  asIso (RelativeCech.sectionsHom f x F)

/-- Degree `n` of `relativeCechSectionsIso` as an isomorphism of abelian groups. -/
def relativeCechSectionsIso_X (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    ((RelativeCech.complex f F).asFunctor.obj (op x.1)).X n ≅
      (Cech.complex (RelativeCech.yonedaBaseChange f x)
          (Cech.inverseImage (YonedaSlice.representative x) F)).X n :=
  HomologicalComplex.Hom.isoApp (relativeCechSectionsIso f x F) n

end
