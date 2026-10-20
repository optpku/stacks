module

public import ReasLib.RingTheory.CompleteIntersection.OverField.Locality
import StacksCheckRecall

/-!
# Local complete intersections over a field

@stack 00SH
-/

@[expose] public section

/- Lemma 10.135.9:

For a finite type `k`-algebra `S`, the following are equivalent:
`S` is a local complete intersection over `k`; every local ring `S_q` for
`q : PrimeSpectrum S` is a complete intersection over `k`; and every localization `S_m` at a
maximal ideal `m` of `S` is a complete intersection over `k`.

This is the source-order `List.TFAE` view of the canonical locality criteria in
`IsLocalCompleteIntersection.iff_forall_prime` and
`IsLocalCompleteIntersection.iff_forall_maximal`.
-/

@[stacks 00SH "(1) iff (2), prime-local criterion"]
#check @IsLocalCompleteIntersection.iff_forall_prime

@[stacks 00SH "(1) iff (3), maximal-local criterion"]
#check @IsLocalCompleteIntersection.iff_forall_maximal
