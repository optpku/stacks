module

public import ReasLib.Topology.Sheaves.Pointwise.Product.AddCommGrp
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat

noncomputable section

universe u

section

/- Exercise 111.32.9 (1): the rule U ↦ ∏_{x ∈ U} A x, with the product-reindexing restriction
maps, defines a sheaf of abelian groups. -/
@[stacks 078Z]
#check (TopCat.Presheaf.PointwiseProduct.isSheaf_addCommGrp :
  ∀ {X : TopCat.{u}} (A : X → AddCommGrpCat.{u}),
    (TopCat.Presheaf.PointwiseProduct.presheaf A).IsSheaf)

/- Exercise 111.32.9 (2): on the indiscrete two-point space with constant integer fibres, the
stalk of the pointwise product sheaf at a point is not isomorphic to the fibre at that point. -/
@[stacks 078Z]
#check (TopCat.Presheaf.PointwiseProduct.not_isIsomorphic_stalk :
  ∀ (x : TopCat.Presheaf.PointwiseProduct.twoPointTrivial),
    ¬ IsIsomorphic
      ((TopCat.Presheaf.PointwiseProduct.presheaf
        TopCat.Presheaf.PointwiseProduct.constantInt).stalk x)
      (TopCat.Presheaf.PointwiseProduct.constantInt x))

end

end
