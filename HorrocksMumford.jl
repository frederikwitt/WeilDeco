# include("path_to/HorrocksMumford.jl")

using Oscar



################################################
# Setup HM-sheaves as modules over the Cox ring
################################################
# As the computation of HM(X,u) may take some time the result are stored in 
# the following dictionary to avoid computing it twice.
HM_computed = Dict{Vector,SubquoModule}()


# HM(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; 
# method::Symbol=:intersec)
# Given a u-matrix and a toric variety X checks whether u is compatible with X 
# and computes then the Cl(X)-graded module HM(u) over the Cox ring of X.
function HM(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	M = get!(() -> compute_HM(X,u,messages;method=method), HM_computed, [X,u,method])
end


# compute_HM
# Given a u-matrix and a toric variety X checks whether u is compatible with X # and computes then the Cl(X)-graded module HM(u) over the Cox ring of X.
function compute_HM(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	if !is_compatible(X,u,messages)
		println("\nError: matrix not compatible")
		return nothing
	end
	if method==:intersec
		return HM_intersection(X,u,messages)
	elseif method==:refhull
		return HM_reflexivehull(X,u,messages)
	else
		println("\nError: supported methods are:\n:intersec\n:refhull")
		return nothing
	end
end


# is_compatible
# Checks whether a u-matrix is compatible, that is,
# 1) square matrix
# 2) only zeros on diagonal
# 3) factors over M.
function is_compatible(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false)
	if number_of_columns(u) != number_of_rows(u) 
		if messages
			println("\nError: matrix must be square")
		end
		return false
	end
	n = number_of_columns(u)
	for i=1:n
		if u[i,i] != 0
			if messages
				println("\nError: u has non-zero entries on diagonal")
			end
			return false
		end
	end
	if n != number_of_rays(X)
		if messages
			println("\nError: u has ", n, " columns, but X has ", number_of_rays(X), " rays")
		end
		return false
	end
        mat=transpose(map_from_torusinvariant_weil_divisor_group_to_class_group(X).map)
	if mat*u==0
		return true
	else
                if messages
                        println("\nError: u does not factor over M")
                end
		return false
	end
end


# HM_intersection
# Given a u-matrix and a toric variety X checks whether u is compatible with X 
# and computes then the Cl(X)-graded module HM(u) over the Cox ring of X using # the intersection-method.
function HM_intersection(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false)
    u_pm = pm_matrix(u)

    R = cox_ring(X)
    R2 = graded_free_module(R,2)

    L_x_hat = []
    for i=1:number_of_generators(R)
    	Li = [ R2([ x_Sigma((u_pm[1])[:,i],R), x_Sigma((u_pm[2])[:,i],R) ]),  R2([R[i],R(0)]),  R2([R(0),R[i]]) ]
    	Li,_ = sub(R2, Li) 
    	push!(L_x_hat, Li )
    end
    
    if messages
    	display(L_x_hat)
    end

    M = L_x_hat[1]
    for i=2:length(L_x_hat)
    	M,_ = intersect(M,L_x_hat[i])
    end

    M = image(map(presentation(M,minimal=true),0))[1]
    
    return twist(M, degree(prod(gens(R))))
end


# HM_reflexivehull
# Given a u-matrix and an (affine) toric variety X checks whether u is 
# compatible with X and computes then the Cl(X)-graded module HM(u) over the 
# Cox ring of X using the reflexive-hull-method.
function HM_reflexivehull(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false)
    u_pm = pm_matrix(u)
    
    R = cox_ring(X)
    R2 = graded_free_module(R,2)
    
    p = prod(gens(R))
    
    prime_gens = (i -> R2([p/R[i]*x_Sigma((u_pm[1])[:,i],R), p/R[i]*x_Sigma((u_pm[2])[:,i],R) ])).(1:number_of_generators(R))
    push!(prime_gens, R2([p, R(0)]), R2([R(0), p]) )

    M, incM = sub(R2, prime_gens)
    
    if messages
    	println("The HM(u)'-module is given by: ")
    	display(M)
    end
    
    R1=graded_free_module(R,1)
    
    #double_dual(M)[1]
    
    #creates the dual spaces: incR2d(R2d[1])(R2[1])=R1[1]
    R2d, incR2d = hom(R2,R1)
    Md, incMd   = hom(M,R1)
    
    #creates the dual map incMD=(incM)^*:R^{2*}\to M^*
    incMD = hom(R2d,Md,[preimage(incMd,compose(incM,incR2d(g))) for g in gens(R2d)])
    
    #creates the double duals
    R2dd, incR2dd = hom(R2d,R1)
    Mdd, incMdd   = hom(Md, R1)
    
    #creates the dual map incMDD=(incMD)^*:M^{**}\to R^{2**}
    incMDD = hom(Mdd,R2dd,[preimage(incR2dd,compose(incMD,incMdd(g))) for g in gens(Mdd)])
        
    #Module iso identifying R2dd with R2
    iso = hom(R2dd,R2,[R2[1],R2[2]])

    #canonical module morphism Mdd\to R2
    inc   = compose(incMDD,iso)
    rhM,_ = image(inc)
    
    return twist(rhM,degree(p))
end


# pm_matrix
# Decomposes an integer matrix u into pair [u_plus,u_minus] of matrices with 
# non-negative entries such that u=u_plus-u_minus.
function pm_matrix(u::ZZMatrix)
	u_plus=matrix(u)
	for i=1:number_of_rows(u)
		for j=1:number_of_columns(u)
			if u_plus[i,j]<0
				u_plus[i,j]=0
			end
		end
	end
	return [u_plus,u_plus-u]
end


# x_Sigma 
# Given a ring R and some vector u_column returns the monomial \prod x_i^u_i.
function x_Sigma(u_column::Vector{ZZRingElem}, R::MPolyDecRing)
	n=length(u_column)
	return prod( (i -> R[i]^(u_column[i])).(1:n) )
end



################################################
# Chern classes
################################################
# dictionaries used for is_num_indecomposable_HM
chow_computed = Dict{NormalToricVariety, MPolyQuoRing}()


# chern(X::NormalToricVariety, u::ZZMatrix,messages::Bool=false; 
# method::Symbol=:intersec)
# Given a matrix u and a projective toric variety X computes the chern class 
# of HM(X,u)
function chern(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	if !is_projective(X)
		println("\nError: the variety is not projective")
		return nothing
	end
	
	M = get!(() -> compute_HM(X,u,messages;method=method), HM_computed, [X,u,method])
	
	return chern(M,get_chow(X),messages)
end


# get_chow
# computes and stores the Chow ring of X in order to avoid "parents must 
# match" issues
function get_chow(X::NormalToricVariety)
    return get!(() -> chow_ring(X), chow_computed, X)
end


# chern(M::Union{SubquoModule,FreeMod}, A::MPolyQuoRing{QQMPolyRingElem}, 
# messages::Bool=false)
# Given a module M over a (Cox) ring and given a (Chow) ring A computes the 
# chern class of the sheaf associated to M in A.
function chern(M::Union{SubquoModule,FreeMod}, A::MPolyQuoRing{QQMPolyRingElem}, messages::Bool=false)
	F=free_resolution(M)
	if messages
		println("Free resolution of M:")
		display(F)
	end
        e=A(1)
        degsD=degree_lifting(base_ring(M),A)
        ch=e
        for i=0:length(F)
                degsF=-degree.(gens(F[i]))
                for D=degsF
                	cOD=sum((k -> D[k]*degsD[k]).(1:length(degsD)))
                	if i%2 == 0
                                ch=ch*(e+cOD)
                        else
                                ch=ch*invert(cOD) 
                        end
                end
        end
        return ch
end


# chern(X::NormalToricVariety, M::SubquoModule, messages::Bool=false) 
# Given a module M over a (Cox) ring and given a (projective) toric variety X
# computes the chern class of the sheaf associated to M in the Chow ring of X.
function chern(X::NormalToricVariety, M::SubquoModule, messages::Bool=false)
	if !is_projective(X)
		println("\nError: the variety is not projective")
		return nothing
	end
	return chern(M,get_chow(X),messages)
end


# degree_lifting
# Given (Cox) ring R and (Chow) ring A returns a list of (linear combinations 
# of) variables such that the corresponding divisors generate A. This lifting 
# assumes that the grading group is some Z^n.
function degree_lifting(R::MPolyDecRing{QQFieldElem, QQMPolyRing},A::MPolyQuoRing{QQMPolyRingElem})
	G = grading_group(R)
	if !is_free(G)
		println("\nError: Grading group is not free (not implemented)")
		return nothing
	end
	degs=(i->(j->(degree.(gens(R)))[i][j]).(1:rank(G))).(1:length(gens(R))) # matrix of degrees
	for submat=combinations(degs,rank(G))
		if abs(det(matrix(ZZ,submat)))==1 # find suitable subset of deg(x_i) that generate G
			baseind=(row -> findfirst(d->row==d,degs)).(submat) # find their positions in matrix of degrees
			basemat=matrix(ZZ,(i->degs[i]).(baseind)) # turn the corresponding degrees into a matrix
			invmat=matrix(A,basemat^(-1)) # inverse to get from generating degree to (linear combination) of variables
			basevars=(i->A[i]).(baseind) # get the variables to the found positions
			return invmat*basevars 
		end
	end
	println("\nError: Grading group not generated by degrees of variables (something is wrong), degrees are:")
	display(degs)
	return nothing
end


# invert
# Given an element c of a (Chow) ring A returns inverse 1-c+c^2-c^3... of 1+c 
# [sic!].
function invert(c::MPolyQuoRingElem{QQMPolyRingElem})
	e=parent(c)(1)
	result=e
	#i=0
	sign=1 # (-1)^i
	ci=e # ci=c^i
	while ci != 0
		#i=i+1
		ci=ci*c
		sign=sign*(-1)
		result = result + sign*ci
	end
	return result
end



################################################
# Indecomposability
################################################
# dictionaries used for is_num_indecomposable_HM
lattice_points_computed = Dict{NormalToricVariety,Vector}()
chern_classes_computed = Dict{NormalToricVariety,Vector}()


# is_num_indecomposable_HM(X::NormalToricVariety, 
# u::ZZMatrix;method::Symbol=:intersec)
# Given a projective toric variety X and a HM-module M, checks whether 
# c(M) = c(O_D1) * c(O_D2). If not, then M is indecomposable; if yes, M might 
# still be indecomposable. As we have O^2 \subseteq M \subset O(-K)^2, any 
# possible direct summand L has to be in \eff(X)\cap(-K_X-\eff(X)).
function is_num_indecomposable_HM(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	if !is_projective(X)
		println("\nError: the variety is not projective")
		return nothing
	end
	
	M = get!(() -> compute_HM(X,u,messages;method=method), HM_computed, [X,u,method])
	return is_num_indecomposable_HM(X,M)
end


# is_num_indecomposable_HM
# Given a toric variety X and a HM-module M, checks whether c(M) = c(O_D1) * 
# c(O_D2). If not, then M is indecomposable; if yes, M might still be 
# indecomposable. As we have O^2 \subseteq M \subset O(-K)^2, any possible 
# direct summand L has to be in \eff(X)\cap(-K_X-\eff(X)).
function is_num_indecomposable_HM(X::NormalToricVariety, M::SubquoModule)
	chern_Ds = get!(() -> compute_chern_Ds(X), chern_classes_computed, X)
        c_HM = chern(X,M)
        for cD1=chern_Ds
                for cD2=chern_Ds
                        if c_HM == cD1*cD2
                                return false
                        end
                end
        end
        return true
end


# compute_chern_Ds
# Given a toric variety X computes the chern classes of all divisors in
# \eff(X)\cap(-K_X-\eff(X)).
function compute_chern_Ds(X::NormalToricVariety)
	lPs = get!(() -> compute_lattice_points(X), lattice_points_computed, X )
	return compute_chern_Ds(X,lPs)
end


# compute_lattice_points
# Given a toric variety X computes all the lattice points in
# eff(X)\cap(-K_X-eff(X)) in Pic(X)\tensor Q.
function compute_lattice_points(X::NormalToricVariety)
        f = map_from_torusinvariant_cartier_divisor_group_to_picard_group(X)
        CDivX = domain(f)
        PicX = codomain(f)
        Q = polyhedron(cone(matrix(f)))
        mK = f(sum( (i -> CDivX[i]).(1:number_of_rays(X)) ))
        P = convex_hull([ getindex(mK,i) for i in 1:rank(PicX) ])
        lPs = lattice_points(intersect(Q,P+(-1)*Q))
	return collect(lPs)
end


# compute_chern_Ds
# Given a toric variety X and lattice points in Pic(X) computes their Chern 
# classes.
function compute_chern_Ds(X::NormalToricVariety, lPs::Vector)
        R = cox_ring(X)
        G = grading_group(R)
        possible_Ds = ( D -> sum( (i -> D[i]*G[i]).(1:rank(G))) ).(lPs)
        O = graded_free_module(cox_ring(X),1)
        A = get_chow(X)
        chern_Ds = ( D -> chern( twist(O,D), A ) ).(possible_Ds)
        return chern_Ds
end



################################################
# Check (local) freeness 
################################################
# is_locally_free_HM(X::NormalToricVariety, u::ZZMatrix, 
# messages::Bool=false;method::Symbol=:intersec)
# Given a matrix u and a toric variety X check whether HM(u) is locally free
# assumes without test that u is compatible with X (can be tested with 
# is_compatible(X,u)) and that X is smooth and semiprojective.
function is_locally_free_HM(X::NormalToricVariety, u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	n=number_of_rows(u)
	if messages
		println("u = ")
		display(u)
	end
	max_cones_mat=maximal_cones(IncidenceMatrix,X)
	u_affines=[]
	for i=1:number_of_maximal_cones(X)
		sigmaind=max_cones_mat[i,:] # list of booleans whether i-th ray belongs to sigma
		sigma=(Polymake.findnz(sigmaind))[1] # get the position of the rays that belong to sigma
		push!(u_affines,u[sigma,sigma])
	end
	for u_affine=u_affines
		if !is_free_affine_HM(u_affine,messages;method=method)
			return false
		end
	end
	return true
end


# is_free_affine_HM
# Given a (compatible) nxn matrix u, the HM(u)-module on An is computed
# and is freeness tested by is_free_affine_module.
function is_free_affine_HM(u::ZZMatrix, messages::Bool=false; method::Symbol=:intersec)
	n=number_of_columns(u)
	An=affine_space(NormalToricVariety,n)
	M=HM(An,u,messages;method=method)
	return is_free_affine_module(M,2,messages)
end


# is_free_affine_module (used by is_free_affine_HM)
# Given a (graded) module M of given rank rk, the rk-th fitting ideal is 
# computed to test freeness.
function is_free_affine_module(M::SubquoModule, rk::Integer=2, messages::Bool=false)
	R=base_ring(M)
	one_ideal=ideal(R,1)
	if messages
		println("Compute ", rk, "-th fitting ideal")
	end
	fitting=fitting_ideal(M,rk)
	if fitting != one_ideal 
		if messages
			println(rk, "-th fitting ideal:")
			display(fitting)
		end
		return false
	end
	return true
end



################################################
# Various
################################################
# kleinschmidt(n::Integer, a::Vector)
# Given an integer n and an ZZ-vector a (of length r) returns the projective 
# bundle morphism P(O + O(a_1) + .. + O(a_r)) -> Pn whose domain is a 
# Hirzebruch-Kleinschmidt variety.
function kleinschmidt(n::Integer, a::Vector)
	r = length(a)
	I = identity_matrix(ZZ,n+r)

	ray_generators = Vector[]
	push!(ray_generators,  sum(i -> -I[i,:], 1:n) + sum(i -> a[i]*I[n+i,:], 1:r) )
	for i=1:n+r
		push!(ray_generators, I[i,:])
	end
	push!(ray_generators, sum(i -> -I[n+i,:], 1:r))

	max_cones = Vector{Integer}[]
	for i=1:n+1
		for j=1:r+1
			cone = collect(1:n+r+2)
			deleteat!(cone, i)
			deleteat!(cone, n+j)
			push!(max_cones,  cone )
		end
	end
	max_cones = incidence_matrix(max_cones)

	X = normal_toric_variety(max_cones, ray_generators)
	Pn = projective_space(NormalToricVariety,n)
	
	return toric_morphism(X, I[:,1:n], Pn)
end
;

	
	
	
