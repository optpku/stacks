module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations.Versality
import StacksCheckRecall

/-!
# Versality at finite type points implies smoothness on predeformations

If an object of a category fibred in groupoids over `(Sch/S)_fppf` is versal
at every finite type point of a locally finite type scheme `U` over a locally
Noetherian base, and the category satisfies (RS), then the associated 2-Yoneda
1-morphism is smooth on predeformations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 98.13.3: if `S` is locally Noetherian, `X` is a category fibred in
groupoids over `(Sch/S)_fppf` satisfying (RS), `U ⟶ S` is locally of finite
type, and `x` over `U` is versal at every finite type point of `U`, then the
2-Yoneda 1-morphism `x : (Sch/U)_fppf ⟶ X` is smooth on predeformations
(98.13.2.1). -/
@[stacks 07XT] #check
  (AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations.of_isVersalAt_finiteTypePoints :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasRimSchlessinger X] {U : Scheme.{u}} (hU : U ⟶ S)
    [LocallyOfFiniteType hU] (x : X.total) (hx : X.p.obj x = Over.mk hU)
    (h_versal : ∀ u : U, IsFiniteTypePoint u → IsVersalAt hU x hx u),
    AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations (yonedaOfObject hU x hx))
