import bauplan
from datetime import datetime


def run_scenario(
    bpln_client: bauplan.Client,
    table_name: str,
    full_user_name,
    branch_name: str,
    starting_branch_name: str,
    s3_uri: str
):
    print(f"Starting the scenario at {datetime.now()}...")
    try:
        # 1. create a branch
        t_branch = bpln_client.create_branch(branch=branch_name, from_ref=starting_branch_name)
        print(f"Created branch {t_branch.name} at {datetime.now()} from {starting_branch_name}.")
        # 2. create a table - this will create a commit
        t_table = client.create_table(
            table=table_name,
            search_uri=s3_uri,
            branch=branch_name
        )
        print(f"Created table {t_table.name} at {datetime.now()} in branch {branch_name}.")
        # 3. check the commit in the history 
        last_commit = client.get_commits(
            branch_name, 
            filter_by_author_name=full_user_name, 
            limit=1
        )[0]
        print(f"Last commit was {last_commit.ref}: {last_commit.message}")
        # the message should contain the table name that we just created 
        # e.g. Create ICEBERG_TABLE bauplan.apoalloytable
        # let's check that
        assert table_name in last_commit.message, f"Table name {table_name} not found in commit message."
        # 4. merge the branch into the starting branch
        client.merge_branch(
            source_ref=branch_name,
            into_branch=starting_branch_name,
        )
        # check the commit again
        # 4. check the commit in the history 
        last_commit = client.get_commits(
            starting_branch_name, 
            filter_by_author_name=full_user_name, 
            limit=1
        )[0]
        print(f"Last commit was {last_commit.ref}: {last_commit.message}")
        # the message should contain the branch name that we just merged
        # e.g. Merge jacopo.alloy_blog_1749811746 into main
        # let's check that
        assert branch_name in last_commit.message, f"Branch name {branch_name} not found in commit message."
    except Exception as e:
        print(f"An error occurred: {e}")
    finally:
        # clean up
        is_deleted = bpln_client.delete_branch(branch_name)
        assert is_deleted, f"Failed to delete branch {branch_name}."
        print(f"Deleted branch {branch_name} at {datetime.now()}.")
        
    print(f"All done at {datetime.now()}: see you, space cowboy!")
    
    return


if __name__ == "__main__":
    from time import time
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--table_name", required=True)
    parser.add_argument("--profile", default='default')
    parser.add_argument("--starting_branch", default='main')
    # we need a parquet file in S3 to create a table as per Bauplan flow
    parser.add_argument("--s3_uri", default='s3://alpha-hello-bauplan/green-taxi/*.parquet')
    # get arguments from the parser into a variable
    args = parser.parse_args()
    profile = args.profile
    table_name = args.table_name
    starting_branch = args.starting_branch
    s3_uri = args.s3_uri
    # start the bauplan client and do some basic checks
    client = bauplan.Client(profile=profile)
    user = client.info().user
    username = user.username
    full_name = user.full_name
    # make sure we have all the info available
    assert username is not None and user is not None
    # make sure the table does NOT exist already in the starting branch
    assert not client.has_table(table=table_name, ref=starting_branch), \
            f"Table {table_name} already exists in branch {starting_branch}. Pick a new one!"
    # create a temporary branch name based on the current time
    temp_branch_name = f"{username}.alloy_blog_{int(time())}"
    run_scenario(
        bpln_client=client,
        table_name=table_name,
        full_user_name=full_name,
        branch_name=temp_branch_name,
        starting_branch_name=starting_branch,
        s3_uri=s3_uri
    )