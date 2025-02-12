R, (x, y, z) = QQ[:x, :y, :z]
A = R[x^3 y^2 z; 1 x^5 y^3]
res1 = Oscar._find_entries_with_least_complexity(A)
SA = Oscar.sparse_matrix(A)
@test res1 == Oscar._find_entries_with_least_complexity(Oscar.sparse_matrix(A))

for i in 1:nrows(A)
  for j in 1:ncols(A)
    res1 = Oscar._apply!([(i, j, :loc)], A)
    res2 = matrix(Oscar._apply!([(i, j, :loc)], SA))
    @test map_entries(f->base_ring(res2)(lift(f)), res1) == res2
    res1 = Oscar._apply!([(i, j, :quo)], A)
    res2 = matrix(Oscar._apply!([(i, j, :quo)], SA))
    @test map_entries(f->base_ring(res2)(lift(f)), res1) == res2
  end
end

n = Oscar.MatrixTreeNode(SA)
Oscar.explore_minimal_complexity(n)

n = Oscar.MatrixTreeNode(A)
Oscar.explore_minimal_complexity(n)

sing = vec(readlines("/home/matthias/Downloads/singular_3_12.dat"))

function check_matroid(i::Int; k::Int=0, parallel::Bool=true, depth::Int=3, width::Int=2)
M = matroid_from_revlex_basis_encoding(sing[i], 3, 12)
#M = moebius_kantor_matroid()
#M = pappus_matroid()
for i in 1:k
  DM = dual_matroid(M)
  M = dual_matroid(principal_extension(DM, matroid_groundset(DM), length(matroid_groundset(DM)) + 1))
end

real_MM = realization_space(M, ground_ring=QQ);
gens(modulus(OO(real_MM)))

D = map_entries(OO(real_MM), jacobi_matrix(gens(modulus(OO(real_MM)))))
@time Oscar._has_locally_constant_rank_parallel(Oscar.MatrixTreeNode(D); depth, width)[1]
end

A = realization_matrix(real_MM)
SA = sparse_matrix(A)
prog1, _ = Oscar.explore_maximal_complexity(Oscar.MatrixTreeNode(A); depth=4, width=7)
prog2, _ = Oscar.explore_maximal_complexity(Oscar.MatrixTreeNode(SA); depth=4, width=7)
@test prog1 == prog2 

prog1, _ = Oscar.explore_minimal_complexity(Oscar.MatrixTreeNode(A); depth=4, width=7)
prog2, _ = Oscar.explore_minimal_complexity(Oscar.MatrixTreeNode(SA); depth=4, width=7)
@test prog1 == prog2 

for (i, code) in enumerate(sing)
  @show i
  M = matroid_from_revlex_basis_encoding(sing[i], 3, 12)
  it = 1
  for i in 1:it
    DM = dual_matroid(M)
    M = dual_matroid(principal_extension(DM, matroid_groundset(DM), length(matroid_groundset(DM)) + 1))
  end

  real_MM = realization_space(M, ground_ring=QQ);
  A = realization_matrix(real_MM)
  @time success, _ = Oscar.has_locally_constant_rank(A; depth=2, width=2)
  @show success
  D = map_entries(OO(real_MM), jacobi_matrix(gens(modulus(OO(real_MM)))))
  @time success, _ = Oscar.has_locally_constant_rank(D; depth=2, width=2)
  @show success
end

