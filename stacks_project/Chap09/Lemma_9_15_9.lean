module

public import ReasLib.FieldTheory.Galois.Counting
import StacksCheckRecall

@[expose] public section

/- Lemma 9.15.9 (Tag 09HS): for a finite extension `E/F`, the number of `F`-automorphisms of
`E` is at most `Field.finSepDegree F E`, with equality exactly when `E/F` is normal. -/
@[stacks 09HS]
#check FieldExtension.natCardGalLeFinSepDegree
#check FieldExtension.natCardGalEqFinSepDegreeIffNormal
