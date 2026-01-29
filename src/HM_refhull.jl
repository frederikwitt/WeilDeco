function HM_refhull(u)
    #check that matrix u of type ZZMatrix is well-defined
    if !(u isa ZZMatrix)
        println("\nError: matrix must be of type ZZMatrix")
        return nothing
    end
    if ncols(u)!=nrows(u) 
        println("\nError: matrix must be square")
        return nothing
    end
    n=ncols(u)    
    for j in 1:n
        if u[j,j]!= 0
            println("\nError: diagonal entries must be 0")
            return nothing
        end
    end
    
    # define the ring in dependence of n
    vars=Symbol.("x" .* string.(1:n))
    R, x=polynomial_ring(QQ,vars)
    o=zero(R)
    
    R1=free_module(R,1)
    R2=free_module(R,2)
    
    # define the generating vectors for the module HM'(u)
    genvec=Vector{FreeModElem{QQMPolyRingElem}}(undef,n+2)
    up=Array{Int}(undef, n, n)
    um=Array{Int}(undef, n, n)
    for i in 1:n
        for j in 1:n
            if u[j,i]>0
                up[i,j]=u[j,i]
                um[i,j]=0
            elseif u[j,i]<0
                up[i,j]=0
                um[i,j]=-u[j,i]
            else
                up[i,j]=0
                um[i,j]=0
            end
        end
        p1=1*x[1]^0
        p2=1*x[1]^0
        for j in 1:n
            p1=p1*x[j]^up[i,j]
            p2=p2*x[j]^um[i,j]
        end
        p=x[1]^0
        for j in 1:n
            if j!=i
                p=p*x[j]
            end
        end
        genvec[i]=R2([p*p1,p*p2])
    end
    prod=x[1]
    for i in 2:n
        prod=prod*x[i]
    end
    genvec[n+1]=R2([prod,o])
    genvec[n+2]=R2([o,prod])
    
    #creates HM'(u) as a submodule of R^2
    M, incM =sub(R2, genvec)
    
    #creates the dual spaces: incR2d(R2d[1])(R2[1])=R1[1]
    R2d, incR2d =hom(R2,R1)
    Md, incMd =hom(M,R1)
    
    #creates the dual map incMD=(incM)^*:R^{2*}\to M^*
    incMD=hom(R2d,Md,[preimage(incMd,compose(incM,incR2d(g))) for g in gens(R2d)])
    
    #creates the doule duals
    R2dd, incR2dd =hom(R2d,R1)
    Mdd, incMdd =hom(Md, R1)
    
    #creates the dual map incMDD=(incMD)^*:M^{**}\to R^{2**}
    incMDD = hom(Mdd,R2dd,[preimage(incR2dd,compose(incMD,incMdd(g))) for g in gens(Mdd)])
        
    #Module iso identifying R2dd with R2
    iso = hom(R2dd,R2,[R2[1],R2[2]])

    #canonical module morphism Mdd\to R2
    inc=compose(incMDD,iso)
    rhM, incrhM=image(inc)
    
    #compute a presentation in order to get possibly less generators
    pres=presentation(rhM,minimal=true)
    N, incN=image(map(pres,0))
    l=length(gens(N))
    genvec=Vector{SubquoModuleElem{QQMPolyRingElem}}(undef,l)
    for i in 1:l
        genvec[i]=N[i]
    end
    rhM, incrhM=sub(R2, genvec)
   
    return R, R2, rhM, incrhM
end


