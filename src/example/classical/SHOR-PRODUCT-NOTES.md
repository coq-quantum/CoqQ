# Finite product counting for Lemma 7.2(2)

This is the combinatorial step of `SHOR-COUNTING-NOTES.md`. Let I be a
nonempty finite index set, X_i finite sets, and l_i : X_i -> K finite labels.
The sets X_i may be different and may be empty. Fix i0 in I. Let c_i(k)
count the elements with label k, and suppose 2 c_i(k) <= |X_i| for every
i other than i0. No restriction on the first coordinate is necessary.

Partition the functions f in the dependent product by their common label.
The constant-label fiber has cardinal product_i c_i(k), by finite function
family counting. Thus the number B of functions with all labels equal is
sum_k product_i c_i(k). For each summand, move the factor 2^(|I|-1)
into the product over i != i0. The coordinate inequalities give

    2^(|I|-1) product_i c_i(k)
      <= c_i0(k) product_(i != i0) |X_i|.

Summing over k and using sum_k c_i0(k)=|X_i0| proves

    2^(|I|-1) B <= product_i |X_i|.

This argument proves a general counting theorem. It does not assume CRT,
the distribution of modular orders, or the desired Shor success bound.
Those number-theory premises must be instantiated by their separate proofs.

Natural-number labels reduce to finite labels without a boundedness premise:
take K to be the ordinals below one plus max_i max_x l_i(x). Every label
belongs to this type by the two finite maximum inequalities, and ordinal
equality is exactly natural-number equality. This yields the same theorem
for logn 2 labels on finite groups.

The direct-compiled module `shor_product_counting.v` proves
`product_half_bound`, `sum_product_half_bound`, `product_card`, `family_card`,
`label_count_sum`, `diagonal_card`, and `diagonal_half_bound`.
`natural_diagonal_half_bound` gives the natural-label variant, with the bound
constructed internally by `label_bound` and `label_bounded`. No boundedness
premise or axiom is added.
