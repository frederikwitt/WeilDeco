using HorrocksMumford
using Oscar
using Test



@testset "HM_affine" begin    
    #error handling of input
    @testset "working error handling" begin
        @testset "wrong matrix type" begin
            u=matrix(QQ,2,2,[0 1;-1 0]) 
            @test HM_affine(u)===nothing
        end
        @testset "nonsquare matrix" begin
            u=matrix(ZZ,2,3,[0 1 0;0 0 1])
            @test HM_affine(u)===nothing
        end
        @testset "nonzero diagonal" begin
            u=matrix(ZZ,2,2,[1 0;0 0])
            @test HM_affine(u)===nothing
        end
    end
    
    #created output is formally valid
    @testset "valid output" begin
        u=matrix(ZZ,2,2,[0 1;-1 0])
        result=HM_affine(u)

        @test result!==nothing
        @test length(result)==4

        R,R2,M,inc=result

        #ring checks
        @test R isa QQMPolyRing
        @test ngens(R)==ncols(u)

        #free module R^2
        @test R2 isa FreeMod
        @test rank(R2)==2

        #submodule and inclusion map
        @test M isa SubquoModule
        @test inc isa SubQuoHom

        #generators live in R^2
        for g in gens(M)
            @test parent(inc(g))==R2
        end
    end

    #edge case
    @testset "zero matrix" begin
        u=zero_matrix(ZZ,2,2)
        result=HM_affine(u)
        @test result!== nothing
        R,R2,M,incM=result
        @test length(gens(M))==2
    end    
end



@testset "HM_refhull" begin
    #error handling of input
    @testset "working error handling" begin
        @testset "wrong matrix type" begin
            u=matrix(QQ,2,2,[0 1;-1 0]) 
            @test HM_refhull(u)===nothing
        end
        @testset "nonsquare matrix" begin
            u=matrix(ZZ,2,3,[0 1 0;0 0 1])
            @test HM_refhull(u)===nothing
        end
        @testset "nonzero diagonal" begin
            u=matrix(ZZ,2,2,[1 0;0 0])
            @test HM_refhull(u)===nothing
        end
    end
    
    #created output is formally valid
    @testset "valid output" begin
        u=matrix(ZZ,2,2,[0 1;-1 0])
        result=HM_refhull(u)

        @test result!==nothing
        @test length(result)==4

        R,R2,M,inc=result

        #ring checks
        @test R isa QQMPolyRing
        @test ngens(R)==ncols(u)

        #free module R^2
        @test R2 isa FreeMod
        @test rank(R2)==2

        #submodule and inclusion map
        @test M isa SubquoModule
        @test inc isa SubQuoHom

        #generators live in R^2
        for g in gens(M)
            @test parent(inc(g))==R2
        end
    end

    #edge case
    @testset "zero matrix" begin
        u=zero_matrix(ZZ,2,2)
        result=HM_refhull(u)
        @test result!== nothing
        R,R2,M,incM=result
        @test length(gens(M))==2
    end    
end



@testset "HM_projective" begin    
    #error handling of input
    @testset "working error handling" begin
        @testset "wrong matrix type" begin
            u=matrix(QQ,3,3,[0 1 0;-1 0 -1;1 -1 1]) 
            @test HM_projective(u)===nothing
        end
        @testset "nonsquare matrix" begin
            u=matrix(ZZ,2,3,[0 1 0;0 0 1])
            @test HM_projective(u)===nothing
        end
        @testset "nonzero diagonal" begin
            u=matrix(ZZ,3,3,[1 0 0;0 1 0;0 1 0])
            @test HM_projective(u)===nothing
        end
        @testset "rows do not add to zero" begin
            u=matrix(ZZ,3,3,[0 1 0;1 0 0;-1 1 0])
            @test HM_projective(u)===nothing
        end
    end
    
    #created output is formally valid
    @testset "valid output" begin
        u=matrix(ZZ,3,3,[0 1 -1;-1 0 1;1 -1 0])
        result=HM_projective(u)

        @test result!==nothing
        @test length(result)==4

        RG,RG2,MG,incG=result

        #ring checks
        @test RG isa MPolyDecRing
        @test ngens(RG)==ncols(u)

        #free module R^2
        @test RG2 isa FreeMod
        @test rank(RG2)==2

        #submodule and inclusion map
        @test MG isa SubquoModule
        @test incG isa SubQuoHom

        #generators live in RG^2
        for g in gens(MG)
            @test parent(incG(g))==RG2
        end
    end

    #edge case
    @testset "zero matrix" begin
        u=zero_matrix(ZZ,3,3)
        result=HM_projective(u)
        @test result!== nothing
        RG,RG2,MG,incG=result
        @test length(gens(MG))==2
    end    
end
