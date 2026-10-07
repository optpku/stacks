module

public import ReasLib.FieldTheory.PBasis
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.46.1

The Frobenius subfield, its compositum with the base field, restricted monomials,
`p`-independence, and `p`-bases are owned by the `FieldExtension.Frobenius` and
`FieldExtension.PBasis` namespaces.

@stack 07P1
-/

/- Definition 15.46.1 (1): `p`-independent families. -/
@[stacks 07P1 "Definition 15.46.1 (1): p-independent family"]
#check @FieldExtension.PBasis.IsIndependent

/- Definition 15.46.1 (2): `p`-bases. -/
@[stacks 07P1 "Definition 15.46.1 (2): p-basis"]
#check @FieldExtension.PBasis.IsBasis

#check @FieldExtension.Frobenius.subfield
#check @FieldExtension.Frobenius.compositum
#check @FieldExtension.PBasis.monomial
#check @FieldExtension.PBasis.isBasis_iff_monomial_span

end
