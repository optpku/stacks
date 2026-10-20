module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Quotient stacks of groupoids in algebraic spaces

Typed forwarding declarations preserve the small quotient and atlas API for source-facing
consumers. The constructions are owned by the shared small quotient module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite AlgebraicSpace
open scoped Bicategory Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack `[U /ₚ R]` associated to a groupoid in algebraic spaces, obtained as the
co-Grothendieck construction of `groupoidPresheaf`. -/
abbrev preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  SmallQuotient.preQuotient G

/-- The projection of `[U /ₚ R]` is the co-Grothendieck projection of `groupoidPresheaf`. -/
theorem preQuotient_p {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.preQuotient.p =
      Pseudofunctor.CoGrothendieck.groupoidPresheafProjection G.groupoidPresheaf :=
  SmallQuotient.preQuotient_p G

/-- The selected stackification presentation of `[U /ₚ R]`. -/
abbrev stackificationPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicGeometry.GroupoidsOver.Stackification.Presentation G.preQuotient.p :=
  SmallQuotient.stackificationPresentation G

/-- The comparison of `stackificationPresentation G` is a stackification of `[U /ₚ R]`. -/
theorem stackificationPresentation_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      G.stackificationPresentation.comparison :=
  SmallQuotient.stackificationPresentation_spec G

/-- The quotient stack `[U / R]` associated to a groupoid in algebraic spaces, obtained by
stackifying `[U /ₚ R]`. -/
abbrev quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  SmallQuotient.quotientStack G

/-- The quotient stack is the target of the selected stackification of `[U /ₚ R]`. -/
theorem quotientStack_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.quotientStack = G.stackificationPresentation.target.toGroupoids :=
  SmallQuotient.quotientStack_spec G

/-- The stackification comparison `1`-morphism `[U /ₚ R] ⟶ [U / R]`. -/
abbrev stackificationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.preQuotient ⟶ G.quotientStack :=
  SmallQuotient.stackificationHom G

/-- `stackificationHom` is a stackification of `[U /ₚ R]`. -/
theorem stackificationHom_isStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.Hom.IsStackification
      (Scheme.fppfTopology.over S) G.stackificationHom :=
  SmallQuotient.stackificationHom_isStackification G

/-- The functor on total categories sending a `T`-valued point of `U` to the corresponding
object of `[U /ₚ R]`. -/
abbrev atlasToPreQuotientFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids.total ⥤ G.preQuotient.total :=
  SmallQuotient.atlasToPreQuotientFunctor G

/-- The base of `atlasToPreQuotientFunctor G x` is the scheme underlying the point `x`. -/
theorem atlasToPreQuotientFunctor_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.U.left.toGroupoids.total) :
    (G.atlasToPreQuotientFunctor.obj x).base = x.unop.fst.unop :=
  SmallQuotient.atlasToPreQuotientFunctor_base G x

/-- The canonical `1`-morphism `𝒮_U ⟶ [U /ₚ R]` sending objects of `U` to objects of the
prestack. -/
abbrev atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.U.left.toGroupoids ⟶ G.preQuotient :=
  SmallQuotient.atlasToPreQuotient G

/-- The atlas `1`-morphism `𝒮_U ⟶ [U / R]`. -/
abbrev atlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids ⟶ G.quotientStack :=
  SmallQuotient.atlas G

/-- The atlas factors as the object inclusion into `[U /ₚ R]` followed by stackification. -/
theorem atlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.atlas = G.atlasToPreQuotient ≫ G.stackificationHom :=
  SmallQuotient.atlas_eq G

end AlgebraicGeometry.GroupoidAlgebraicSpace
