module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import StacksCheckRecall

@[expose] public section


universe w vF v u

namespace CategoryTheory
namespace Pseudofunctor.CoGrothendieck

open Functor
open Opposite
open scoped Bicategory

variable {𝒞 : Type u} [Category.{v} 𝒞]
variable {F : 𝒞ᵒᵖ ⥤ Cat.{vF, w}}
variable {X Y : CoGrothendieck F.toPseudofunctor'}
variable {R S : 𝒞} (a : F.obj (op S)) (f : R ⟶ S)

/- The installed `CoGrothendieck` owner and its `Hom` and category instances give exactly the
source's pairs `(U, x)`, pairs `(f, φ)`, and composition formula. Its `forget`,
`domainCartesianLift`, and `cartesianLift` API then gives the projection and the lift `(f, 𝟙)`,
while `isStronglyCartesian_homCartesianLift` and the canonical `IsFibered` instance prove the
required universal property. These owners are formulated for pseudofunctors; the verified bridge
`Functor.toPseudofunctor'` changes only the packaging of the source's ordinary
`F : 𝒞ᵒᵖ ⥤ Cat`, so specializing every owner to `F.toPseudofunctor'` recovers the source
verbatim and leaves the reusable pseudofunctorial API available to later items. The fiber hom
universe `vF` is independent of the base hom universe `v`. -/

/- Example 4.36.1 (1): objects of the associated category are the canonical base-fibre pairs in
`CoGrothendieck F.toPseudofunctor'`. -/
@[stacks 02XV "objects as base-fibre pairs"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck F.toPseudofunctor' :
  Type max u w)

/- Example 4.36.1 (2): morphisms are the canonical pairs of a base arrow `f : V ⟶ U` and a
fibre arrow `y ⟶ F.map f.op |>.obj x`. -/
@[stacks 02XV "morphisms as base arrows with fibre arrows"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.Hom X Y : Type (max v vF))

/- Example 4.36.1 (3): the identity and composition operations are those of the canonical
co-Grothendieck category structure. -/
@[stacks 02XV "identity and composition in the associated category"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.categoryStruct :
  CategoryStruct.{max v vF} (CoGrothendieck F.toPseudofunctor'))

/- Example 4.36.1 (4): the operations above satisfy the category laws. -/
@[stacks 02XV "category laws for the associated category"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.category :
  Category.{max v vF} (CoGrothendieck F.toPseudofunctor'))

/- Example 4.36.1 (5): the functor `p_F` is the canonical projection to the base category. -/
@[stacks 02XV "projection to the base category"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor' :
  CoGrothendieck F.toPseudofunctor' ⥤ 𝒞)

/- Example 4.36.1 (6): the object `(V, F.map f.op |>.obj x)` is the domain of the canonical lift
over `f : V ⟶ U`. -/
@[stacks 02XV "domain object of the canonical lift"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.domainCartesianLift a f :
  CoGrothendieck F.toPseudofunctor')

/- Example 4.36.1 (7): the source lift `(f, 𝟙)` is the canonical `cartesianLift`. -/
@[stacks 02XV "canonical lift given by the fibre identity"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift
    (F := F.toPseudofunctor') a f :
  domainCartesianLift (F := F.toPseudofunctor') a f ⟶
    (⟨S, a⟩ : CoGrothendieck F.toPseudofunctor'))

/- Example 4.36.1 (8): the canonical lift lies over the prescribed base morphism `f`. -/
@[stacks 02XV "canonical morphism lies over the base arrow"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.isHomLift_cartesianLift
    (F := F.toPseudofunctor') (a := a) (f := f) :
  Functor.IsHomLift (forget F.toPseudofunctor') f
    (cartesianLift (F := F.toPseudofunctor') a f))

/- Example 4.36.1 (9): the canonical lift `(f, 𝟙)` is strongly cartesian. -/
@[stacks 02XV "strong cartesianness of the canonical lift"]
#check (CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := F.toPseudofunctor') a f :
  Functor.IsStronglyCartesian
    (forget F.toPseudofunctor') f
    (cartesianLift (F := F.toPseudofunctor') a f))

/- Example 4.36.1 (10): after the bridge `F.toPseudofunctor'`, the canonical projection is a
fibred category over `𝒞`. -/
@[stacks 02XV "fibredness of the co-Grothendieck projection"]
#check (inferInstance : (forget F.toPseudofunctor').IsFibered)

end Pseudofunctor.CoGrothendieck
end CategoryTheory
